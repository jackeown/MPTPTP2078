%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWENWCulDP

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:49 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 256 expanded)
%              Number of leaves         :   33 (  89 expanded)
%              Depth                    :   15
%              Number of atoms          : 1114 (3608 expanded)
%              Number of equality atoms :   19 (  97 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( X21
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( k1_funct_1 @ X20 @ X19 ) ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

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

thf('6',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('8',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('27',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X41 ) @ X37 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( X21
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('43',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('46',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( m1_subset_1 @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X38 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('55',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( r2_hidden @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['32','37'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X42: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X42 ) )
      | ~ ( r2_hidden @ X42 @ sk_C )
      | ~ ( m1_subset_1 @ X42 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('70',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['68','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('84',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X25 ) ) )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('88',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X24 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('89',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(clc,[status(thm)],['86','89'])).

thf('91',plain,(
    $false ),
    inference(demod,[status(thm)],['24','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rWENWCulDP
% 0.11/0.33  % Computer   : n002.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:36:22 EST 2020
% 0.18/0.33  % CPUTime    : 
% 0.18/0.33  % Running portfolio for 600 s
% 0.18/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.33  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 311 iterations in 0.212s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.65  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.65  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.45/0.65  thf(d1_xboole_0, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf(t8_funct_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.65       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.45/0.65         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.65           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.45/0.65          | ((X21) != (k1_funct_1 @ X20 @ X19))
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.45/0.65          | ~ (v1_funct_1 @ X20)
% 0.45/0.65          | ~ (v1_relat_1 @ X20))),
% 0.45/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X20)
% 0.45/0.65          | ~ (v1_funct_1 @ X20)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ X19 @ (k1_funct_1 @ X20 @ X19)) @ X20)
% 0.45/0.65          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X20)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['1'])).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.65          | (r2_hidden @ 
% 0.45/0.65             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.45/0.65              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.45/0.65             X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '2'])).
% 0.45/0.65  thf('4', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_funct_1 @ X0)
% 0.45/0.65          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.45/0.65          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.65  thf(t116_funct_2, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65       ( ![E:$i]:
% 0.45/0.65         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.45/0.65              ( ![F:$i]:
% 0.45/0.65                ( ( m1_subset_1 @ F @ A ) =>
% 0.45/0.65                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.45/0.65                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.65            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65          ( ![E:$i]:
% 0.45/0.65            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.45/0.65                 ( ![F:$i]:
% 0.45/0.65                   ( ( m1_subset_1 @ F @ A ) =>
% 0.45/0.65                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.45/0.65                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k7_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.45/0.65          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.65           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('10', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.65  thf(t143_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ C ) =>
% 0.45/0.65       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.65         ( ?[D:$i]:
% 0.45/0.65           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.65             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.65             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.45/0.65          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 0.45/0.65          | ~ (v1_relat_1 @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.65        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(cc2_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X11 : $i, X12 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.45/0.65          | (v1_relat_1 @ X11)
% 0.45/0.65          | ~ (v1_relat_1 @ X12))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.65  thf(fc6_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.65  thf('17', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.65  thf('20', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      ((~ (v1_xboole_0 @ sk_D_1)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.65        | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['5', '20'])).
% 0.45/0.65  thf('22', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('24', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.45/0.65  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(t52_relset_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.65           ( ![C:$i]:
% 0.45/0.65             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.45/0.65               ( ![D:$i]:
% 0.45/0.65                 ( ( m1_subset_1 @
% 0.45/0.65                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.45/0.65                   ( ![E:$i]:
% 0.45/0.65                     ( ( m1_subset_1 @ E @ A ) =>
% 0.45/0.65                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.45/0.65                         ( ?[F:$i]:
% 0.45/0.65                           ( ( r2_hidden @ F @ B ) & 
% 0.45/0.65                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.45/0.65                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ X36)
% 0.45/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.65          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X41) @ 
% 0.45/0.65             X37)
% 0.45/0.65          | ~ (m1_subset_1 @ X41 @ X39)
% 0.45/0.65          | (v1_xboole_0 @ X38)
% 0.45/0.65          | (v1_xboole_0 @ X39))),
% 0.45/0.65      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.65          | (v1_xboole_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.45/0.65             sk_D_1)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['26', '27'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.65           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.65          | (v1_xboole_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.65          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.45/0.65             sk_D_1)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_C)
% 0.45/0.65        | (r2_hidden @ 
% 0.45/0.65           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.45/0.65        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.45/0.65        | (v1_xboole_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(dt_k7_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.45/0.65         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.45/0.65          | (m1_subset_1 @ (k7_relset_1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.45/0.65             (k1_zfmisc_1 @ X30)))),
% 0.45/0.65      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.45/0.65          (k1_zfmisc_1 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf(t4_subset, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.65       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.45/0.65          | (m1_subset_1 @ X8 @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.45/0.65          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.65  thf('38', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '37'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_C)
% 0.45/0.65        | (r2_hidden @ 
% 0.45/0.65           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.45/0.65        | (v1_xboole_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['31', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.65         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.45/0.65          | ((X21) = (k1_funct_1 @ X20 @ X19))
% 0.45/0.65          | ~ (v1_funct_1 @ X20)
% 0.45/0.65          | ~ (v1_relat_1 @ X20))),
% 0.45/0.65      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.65        | (v1_xboole_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_C)
% 0.45/0.65        | ~ (v1_relat_1 @ sk_D_1)
% 0.45/0.65        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.65        | ((sk_E)
% 0.45/0.65            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.65      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.65  thf('43', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('44', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.65        | (v1_xboole_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_C)
% 0.45/0.65        | ((sk_E)
% 0.45/0.65            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.45/0.65      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.45/0.65  thf('45', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ X36)
% 0.45/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.65          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.45/0.65          | (m1_subset_1 @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X38)
% 0.45/0.65          | ~ (m1_subset_1 @ X41 @ X39)
% 0.45/0.65          | (v1_xboole_0 @ X38)
% 0.45/0.65          | (v1_xboole_0 @ X39))),
% 0.45/0.65      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.45/0.65  thf('48', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.65          | (v1_xboole_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.65          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.65           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('50', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.65          | (v1_xboole_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.65          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['48', '49'])).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_C)
% 0.45/0.65        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.65        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.45/0.65        | (v1_xboole_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['45', '50'])).
% 0.45/0.65  thf('52', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.45/0.65      inference('sup-', [status(thm)], ['32', '37'])).
% 0.45/0.65  thf('53', plain,
% 0.45/0.65      (((v1_xboole_0 @ sk_C)
% 0.45/0.65        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_A)
% 0.45/0.65        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.65      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.65  thf('54', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.65  thf('55', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ X36)
% 0.45/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.45/0.65          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.45/0.65          | (r2_hidden @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X36)
% 0.45/0.65          | ~ (m1_subset_1 @ X41 @ X39)
% 0.45/0.65          | (v1_xboole_0 @ X38)
% 0.45/0.65          | (v1_xboole_0 @ X39))),
% 0.45/0.65      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.65          | (v1_xboole_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.65          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.65           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((v1_xboole_0 @ sk_B_1)
% 0.45/0.65          | (v1_xboole_0 @ sk_A)
% 0.45/0.65          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.45/0.65          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.45/0.65          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.45/0.65          | (v1_xboole_0 @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['57', '58'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.66      (((v1_xboole_0 @ sk_C)
% 0.45/0.66        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.45/0.66        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['54', '59'])).
% 0.45/0.66  thf('61', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.45/0.66      inference('sup-', [status(thm)], ['32', '37'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (((v1_xboole_0 @ sk_C)
% 0.45/0.66        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X42 : $i]:
% 0.45/0.66         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X42))
% 0.45/0.66          | ~ (r2_hidden @ X42 @ sk_C)
% 0.45/0.66          | ~ (m1_subset_1 @ X42 @ sk_A))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('64', plain,
% 0.45/0.66      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_C)
% 0.45/0.66        | ~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.45/0.66        | ((sk_E)
% 0.45/0.66            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (((v1_xboole_0 @ sk_B_1)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_C)
% 0.45/0.66        | ((sk_E)
% 0.45/0.66            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.45/0.66        | (v1_xboole_0 @ sk_C)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['53', '64'])).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.45/0.66        | (v1_xboole_0 @ sk_C)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['65'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      ((((sk_E) != (sk_E))
% 0.45/0.66        | (v1_xboole_0 @ sk_C)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_B_1)
% 0.45/0.66        | (v1_xboole_0 @ sk_B_1)
% 0.45/0.66        | (v1_xboole_0 @ sk_A)
% 0.45/0.66        | (v1_xboole_0 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['44', '66'])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['67'])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.45/0.66          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 0.45/0.66          | ~ (v1_relat_1 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['69', '70'])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X1)
% 0.45/0.66          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.45/0.66           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf('78', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('79', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['73', '78'])).
% 0.45/0.66  thf('80', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('81', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['79', '80'])).
% 0.45/0.66  thf('82', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('clc', [status(thm)], ['68', '81'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc4_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.45/0.66           ( v1_xboole_0 @ C ) ) ) ))).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ X25)
% 0.45/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X25)))
% 0.45/0.66          | (v1_xboole_0 @ X26))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.45/0.66  thf('85', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['83', '84'])).
% 0.45/0.66  thf('86', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_D_1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['82', '85'])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc3_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_xboole_0 @ A ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66           ( v1_xboole_0 @ C ) ) ) ))).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ X22)
% 0.45/0.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X24)))
% 0.45/0.66          | (v1_xboole_0 @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.45/0.66  thf('89', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '88'])).
% 0.45/0.66  thf('90', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.45/0.66      inference('clc', [status(thm)], ['86', '89'])).
% 0.45/0.66  thf('91', plain, ($false), inference('demod', [status(thm)], ['24', '90'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
