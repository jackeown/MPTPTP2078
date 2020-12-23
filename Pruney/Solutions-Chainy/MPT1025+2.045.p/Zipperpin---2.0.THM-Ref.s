%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CLNbqjdTPL

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:49 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 517 expanded)
%              Number of leaves         :   36 ( 166 expanded)
%              Depth                    :   16
%              Number of atoms          : 1279 (7526 expanded)
%              Number of equality atoms :   28 ( 208 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( ( k7_relset_1 @ X30 @ X31 @ X29 @ X32 )
        = ( k9_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t22_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X35 @ X33 ) @ X33 )
      | ( ( k1_relset_1 @ X33 @ X34 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t22_relset_1])).

thf('17',plain,
    ( ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ( r2_hidden @ ( sk_D_1 @ sk_D_2 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,
    ( ( ( k1_relat_1 @ sk_D_2 )
      = sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_relset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_hidden @ X43 @ ( k7_relset_1 @ X40 @ X41 @ X39 @ X38 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X43 @ X39 @ X40 @ X38 ) @ X43 ) @ X39 )
      | ~ ( m1_subset_1 @ X43 @ X41 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X0 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X0 ) @ sk_D_2 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_E_1 ) @ sk_D_2 )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('33',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('35',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_E_1 ) @ sk_D_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','37'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('42',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_hidden @ X43 @ ( k7_relset_1 @ X40 @ X41 @ X39 @ X38 ) )
      | ( m1_subset_1 @ ( sk_F @ X43 @ X39 @ X40 @ X38 ) @ X40 )
      | ~ ( m1_subset_1 @ X43 @ X41 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['31','36'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X43: $i] :
      ( ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( r2_hidden @ X43 @ ( k7_relset_1 @ X40 @ X41 @ X39 @ X38 ) )
      | ( r2_hidden @ ( sk_F @ X43 @ X39 @ X40 @ X38 ) @ X38 )
      | ~ ( m1_subset_1 @ X43 @ X41 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_2 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_2 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['31','36'])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X44: $i] :
      ( ( sk_E_1
       != ( k1_funct_1 @ sk_D_2 @ X44 ) )
      | ~ ( r2_hidden @ X44 @ sk_C )
      | ~ ( m1_subset_1 @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) @ sk_A )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,
    ( ( sk_E_1
     != ( k1_funct_1 @ sk_D_2 @ ( sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_E_1 != sk_E_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['67','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('83',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X19 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('87',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) )
      | ( X18
       != ( k1_funct_1 @ X17 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('88',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X16 @ ( k1_funct_1 @ X17 @ X16 ) ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( sk_D @ X15 @ X13 @ X14 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['9','10'])).

thf('103',plain,(
    ~ ( v1_xboole_0 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['85','103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_D_2 )
    = sk_A ),
    inference(demod,[status(thm)],['23','104'])).

thf('106',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['85','103'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['14','105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CLNbqjdTPL
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:01:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 202 iterations in 0.113s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.38/0.56  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.38/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.38/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.38/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.38/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.38/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.56  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.38/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(t116_funct_2, conjecture,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.56       ( ![E:$i]:
% 0.38/0.56         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.38/0.56              ( ![F:$i]:
% 0.38/0.56                ( ( m1_subset_1 @ F @ A ) =>
% 0.38/0.56                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.38/0.56                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.38/0.56            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.56          ( ![E:$i]:
% 0.38/0.56            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.38/0.56                 ( ![F:$i]:
% 0.38/0.56                   ( ( m1_subset_1 @ F @ A ) =>
% 0.38/0.56                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.38/0.56                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.38/0.56  thf('0', plain,
% 0.38/0.56      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k7_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.38/0.56  thf('2', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.38/0.56          | ((k7_relset_1 @ X30 @ X31 @ X29 @ X32) = (k9_relat_1 @ X29 @ X32)))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.38/0.56           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.56  thf(t143_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ C ) =>
% 0.38/0.56       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.38/0.56         ( ?[D:$i]:
% 0.38/0.56           ( ( r2_hidden @ D @ B ) & 
% 0.38/0.56             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.38/0.56             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.38/0.56  thf('5', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.38/0.56          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k1_relat_1 @ X15))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.56  thf('6', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ sk_D_2)
% 0.38/0.56        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc2_relat_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_relat_1 @ A ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      (![X8 : $i, X9 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.38/0.56          | (v1_relat_1 @ X8)
% 0.38/0.56          | ~ (v1_relat_1 @ X9))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.38/0.56  thf(fc6_relat_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.56  thf('10', plain,
% 0.38/0.56      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.38/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.56  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_1) @ (k1_relat_1 @ sk_D_2))),
% 0.38/0.56      inference('demod', [status(thm)], ['6', '11'])).
% 0.38/0.56  thf(d1_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('14', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.38/0.56  thf('15', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t22_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.38/0.56       ( ( ![D:$i]:
% 0.38/0.56           ( ~( ( r2_hidden @ D @ B ) & 
% 0.38/0.56                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.38/0.56         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.38/0.56         ((r2_hidden @ (sk_D_1 @ X35 @ X33) @ X33)
% 0.38/0.56          | ((k1_relset_1 @ X33 @ X34 @ X35) = (X33))
% 0.38/0.56          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.38/0.56      inference('cnf', [status(esa)], [t22_relset_1])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      ((((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (sk_A))
% 0.38/0.56        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.38/0.56         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 0.38/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.38/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      ((((k1_relat_1 @ sk_D_2) = (sk_A))
% 0.38/0.56        | (r2_hidden @ (sk_D_1 @ sk_D_2 @ sk_A) @ sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['17', '20'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      ((((k1_relat_1 @ sk_D_2) = (sk_A)) | ~ (v1_xboole_0 @ sk_A))),
% 0.38/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.56  thf('24', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.56  thf('25', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(t52_relset_1, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.38/0.56       ( ![B:$i]:
% 0.38/0.56         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.38/0.56           ( ![C:$i]:
% 0.38/0.56             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.38/0.56               ( ![D:$i]:
% 0.38/0.56                 ( ( m1_subset_1 @
% 0.38/0.56                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.38/0.56                   ( ![E:$i]:
% 0.38/0.56                     ( ( m1_subset_1 @ E @ A ) =>
% 0.38/0.56                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.38/0.56                         ( ?[F:$i]:
% 0.38/0.56                           ( ( r2_hidden @ F @ B ) & 
% 0.38/0.56                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.38/0.56                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.56  thf('26', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X38)
% 0.38/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.38/0.56          | ~ (r2_hidden @ X43 @ (k7_relset_1 @ X40 @ X41 @ X39 @ X38))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ (sk_F @ X43 @ X39 @ X40 @ X38) @ X43) @ 
% 0.38/0.56             X39)
% 0.38/0.56          | ~ (m1_subset_1 @ X43 @ X41)
% 0.38/0.56          | (v1_xboole_0 @ X40)
% 0.38/0.56          | (v1_xboole_0 @ X41))),
% 0.38/0.56      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.38/0.56  thf('27', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ sk_B_1)
% 0.38/0.56          | (v1_xboole_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X0) @ 
% 0.38/0.56             sk_D_2)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.38/0.56          | (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.38/0.56           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ sk_B_1)
% 0.38/0.56          | (v1_xboole_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X0) @ 
% 0.38/0.56             sk_D_2)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.38/0.56          | (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_C)
% 0.38/0.56        | (r2_hidden @ 
% 0.38/0.56           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_E_1) @ 
% 0.38/0.56           sk_D_2)
% 0.38/0.56        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['24', '29'])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('32', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(dt_k7_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.56       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.38/0.56         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.38/0.56          | (m1_subset_1 @ (k7_relset_1 @ X23 @ X24 @ X22 @ X25) @ 
% 0.38/0.56             (k1_zfmisc_1 @ X24)))),
% 0.38/0.56      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0) @ 
% 0.38/0.56          (k1_zfmisc_1 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.56  thf(t4_subset, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.38/0.56       ( m1_subset_1 @ A @ C ) ))).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X5 @ X6)
% 0.38/0.56          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.38/0.56          | (m1_subset_1 @ X5 @ X7))),
% 0.38/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.38/0.56          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.38/0.56  thf('37', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '36'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_C)
% 0.38/0.56        | (r2_hidden @ 
% 0.38/0.56           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_E_1) @ 
% 0.38/0.56           sk_D_2)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['30', '37'])).
% 0.38/0.56  thf(t8_funct_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.38/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.38/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.38/0.56           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.38/0.56  thf('39', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.56         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.38/0.56          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_D_2)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.56        | ((sk_E_1)
% 0.38/0.56            = (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf('41', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('42', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | ((sk_E_1)
% 0.38/0.56            = (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.38/0.56      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.38/0.56  thf('44', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X38)
% 0.38/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.38/0.56          | ~ (r2_hidden @ X43 @ (k7_relset_1 @ X40 @ X41 @ X39 @ X38))
% 0.38/0.56          | (m1_subset_1 @ (sk_F @ X43 @ X39 @ X40 @ X38) @ X40)
% 0.38/0.56          | ~ (m1_subset_1 @ X43 @ X41)
% 0.38/0.56          | (v1_xboole_0 @ X40)
% 0.38/0.56          | (v1_xboole_0 @ X41))),
% 0.38/0.56      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ sk_B_1)
% 0.38/0.56          | (v1_xboole_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.56          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.38/0.56          | (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['45', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.38/0.56           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ sk_B_1)
% 0.38/0.56          | (v1_xboole_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.56          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ sk_A)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.38/0.56          | (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['47', '48'])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_C)
% 0.38/0.56        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.38/0.56        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['44', '49'])).
% 0.38/0.56  thf('51', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '36'])).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_C)
% 0.38/0.56        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['50', '51'])).
% 0.38/0.56  thf('53', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['0', '3'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X43 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ X38)
% 0.38/0.56          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.38/0.56          | ~ (r2_hidden @ X43 @ (k7_relset_1 @ X40 @ X41 @ X39 @ X38))
% 0.38/0.56          | (r2_hidden @ (sk_F @ X43 @ X39 @ X40 @ X38) @ X38)
% 0.38/0.56          | ~ (m1_subset_1 @ X43 @ X41)
% 0.38/0.56          | (v1_xboole_0 @ X40)
% 0.38/0.56          | (v1_xboole_0 @ X41))),
% 0.38/0.56      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ sk_B_1)
% 0.38/0.56          | (v1_xboole_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.56          | (r2_hidden @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X1))
% 0.38/0.56          | (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['54', '55'])).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.38/0.56           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('58', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ sk_B_1)
% 0.38/0.56          | (v1_xboole_0 @ sk_A)
% 0.38/0.56          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.38/0.56          | (r2_hidden @ (sk_F @ X0 @ sk_D_2 @ sk_A @ X1) @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_2 @ X1))
% 0.38/0.56          | (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_C)
% 0.38/0.56        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C)
% 0.38/0.56        | ~ (m1_subset_1 @ sk_E_1 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['53', '58'])).
% 0.38/0.56  thf('60', plain, ((m1_subset_1 @ sk_E_1 @ sk_B_1)),
% 0.38/0.56      inference('sup-', [status(thm)], ['31', '36'])).
% 0.38/0.56  thf('61', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_C)
% 0.38/0.56        | (r2_hidden @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_C)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      (![X44 : $i]:
% 0.38/0.56         (((sk_E_1) != (k1_funct_1 @ sk_D_2 @ X44))
% 0.38/0.56          | ~ (r2_hidden @ X44 @ sk_C)
% 0.38/0.56          | ~ (m1_subset_1 @ X44 @ sk_A))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C) @ sk_A)
% 0.38/0.56        | ((sk_E_1)
% 0.38/0.56            != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['61', '62'])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | ((sk_E_1)
% 0.38/0.56            != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['52', '63'])).
% 0.38/0.56  thf('65', plain,
% 0.38/0.56      ((((sk_E_1)
% 0.38/0.56          != (k1_funct_1 @ sk_D_2 @ (sk_F @ sk_E_1 @ sk_D_2 @ sk_A @ sk_C)))
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('simplify', [status(thm)], ['64'])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      ((((sk_E_1) != (sk_E_1))
% 0.38/0.56        | (v1_xboole_0 @ sk_C)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_B_1)
% 0.38/0.56        | (v1_xboole_0 @ sk_A)
% 0.38/0.56        | (v1_xboole_0 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '65'])).
% 0.38/0.56  thf('67', plain,
% 0.38/0.56      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.38/0.56      inference('simplify', [status(thm)], ['66'])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.38/0.56          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ X13)
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.38/0.56             X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('72', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X1)
% 0.38/0.56          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('74', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('sup-', [status(thm)], ['73', '74'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_2 @ X0)
% 0.38/0.56           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.56  thf('77', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.38/0.56  thf('78', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['72', '77'])).
% 0.38/0.56  thf('79', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('80', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.38/0.56      inference('demod', [status(thm)], ['78', '79'])).
% 0.38/0.56  thf('81', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('clc', [status(thm)], ['67', '80'])).
% 0.38/0.56  thf('82', plain,
% 0.38/0.56      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf(cc4_relset_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( v1_xboole_0 @ A ) =>
% 0.38/0.56       ( ![C:$i]:
% 0.38/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.38/0.56           ( v1_xboole_0 @ C ) ) ) ))).
% 0.38/0.56  thf('83', plain,
% 0.38/0.56      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ X19)
% 0.38/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X19)))
% 0.38/0.56          | (v1_xboole_0 @ X20))),
% 0.38/0.56      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.38/0.56  thf('84', plain, (((v1_xboole_0 @ sk_D_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['82', '83'])).
% 0.38/0.56  thf('85', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['81', '84'])).
% 0.38/0.56  thf('86', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X16 @ (k1_relat_1 @ X17))
% 0.38/0.56          | ((X18) != (k1_funct_1 @ X17 @ X16))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | ~ (v1_relat_1 @ X17))),
% 0.38/0.56      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (![X16 : $i, X17 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X17)
% 0.38/0.56          | ~ (v1_funct_1 @ X17)
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ X16 @ (k1_funct_1 @ X17 @ X16)) @ X17)
% 0.38/0.56          | ~ (r2_hidden @ X16 @ (k1_relat_1 @ X17)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['87'])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.38/0.56              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.38/0.56             X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['86', '88'])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      (![X0 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.38/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['89', '90'])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.38/0.56          | (r2_hidden @ (sk_D @ X15 @ X13 @ X14) @ (k1_relat_1 @ X15))
% 0.38/0.56          | ~ (v1_relat_1 @ X15))),
% 0.38/0.56      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.38/0.56          | ~ (v1_relat_1 @ X1)
% 0.38/0.56          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.38/0.56             (k1_relat_1 @ X1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.38/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_relat_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.38/0.56          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['94', '95'])).
% 0.38/0.56  thf('97', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (~ (v1_xboole_0 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['91', '96'])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.38/0.56          | ~ (v1_relat_1 @ X0)
% 0.38/0.56          | ~ (v1_funct_1 @ X0)
% 0.38/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['97'])).
% 0.38/0.56  thf('99', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.38/0.56      inference('demod', [status(thm)], ['75', '76'])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      ((~ (v1_xboole_0 @ sk_D_2)
% 0.38/0.56        | ~ (v1_funct_1 @ sk_D_2)
% 0.38/0.56        | ~ (v1_relat_1 @ sk_D_2))),
% 0.38/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.38/0.56  thf('101', plain, ((v1_funct_1 @ sk_D_2)),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('102', plain, ((v1_relat_1 @ sk_D_2)),
% 0.38/0.56      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.56  thf('103', plain, (~ (v1_xboole_0 @ sk_D_2)),
% 0.38/0.56      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.38/0.56  thf('104', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['85', '103'])).
% 0.38/0.56  thf('105', plain, (((k1_relat_1 @ sk_D_2) = (sk_A))),
% 0.38/0.56      inference('demod', [status(thm)], ['23', '104'])).
% 0.38/0.56  thf('106', plain, ((v1_xboole_0 @ sk_A)),
% 0.38/0.56      inference('clc', [status(thm)], ['85', '103'])).
% 0.38/0.56  thf('107', plain, ($false),
% 0.38/0.56      inference('demod', [status(thm)], ['14', '105', '106'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
