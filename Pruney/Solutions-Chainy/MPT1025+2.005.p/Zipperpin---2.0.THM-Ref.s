%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JwxzXW0kE7

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 329 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :   16
%              Number of atoms          : 1304 (4780 expanded)
%              Number of equality atoms :   20 ( 129 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) )
      | ( X15
       != ( k1_funct_1 @ X14 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ ( k1_funct_1 @ X14 @ X13 ) ) @ X14 )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X14 ) ) ) ),
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

thf('6',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

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

thf('13',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X21 ) ) )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('31',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
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

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_hidden @ X35 @ ( k7_relset_1 @ X32 @ X33 @ X31 @ X30 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X35 @ X31 @ X32 @ X30 ) @ X35 ) @ X31 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( m1_subset_1 @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_2 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( X15
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_hidden @ X35 @ ( k7_relset_1 @ X32 @ X33 @ X31 @ X30 ) )
      | ( m1_subset_1 @ ( sk_F @ X35 @ X31 @ X32 @ X30 ) @ X32 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['38','43'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X35: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_hidden @ X35 @ ( k7_relset_1 @ X32 @ X33 @ X31 @ X30 ) )
      | ( r2_hidden @ ( sk_F @ X35 @ X31 @ X32 @ X30 ) @ X30 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_2 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_E @ sk_B_2 ),
    inference('sup-',[status(thm)],['38','43'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X36: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X36 ) )
      | ~ ( r2_hidden @ X36 @ sk_C )
      | ~ ( m1_subset_1 @ X36 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['59','70'])).

thf('72',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('81',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['74','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('86',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_2 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('92',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('95',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('97',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('98',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('100',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X12 )
      | ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ X12 ) )
      | ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('104',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['90','108'])).

thf('110',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(demod,[status(thm)],['28','109'])).

thf('111',plain,(
    $false ),
    inference(demod,[status(thm)],['25','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JwxzXW0kE7
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:28:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 161 iterations in 0.115s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.56  thf(d1_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.56  thf(t8_funct_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.21/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.21/0.56           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X13 @ (k1_relat_1 @ X14))
% 0.21/0.56          | ((X15) != (k1_funct_1 @ X14 @ X13))
% 0.21/0.56          | (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.21/0.56          | ~ (v1_funct_1 @ X14)
% 0.21/0.57          | ~ (v1_relat_1 @ X14))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X14)
% 0.21/0.57          | ~ (v1_funct_1 @ X14)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ X13 @ (k1_funct_1 @ X14 @ X13)) @ X14)
% 0.21/0.57          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X14)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.57          | (r2_hidden @ 
% 0.21/0.57             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.21/0.57              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.21/0.57             X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['0', '2'])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.21/0.57          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf(t143_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( v1_relat_1 @ C ) =>
% 0.21/0.57       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.57         ( ?[D:$i]:
% 0.21/0.57           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.57             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.57             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.21/0.57          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ (k1_relat_1 @ X12))
% 0.21/0.57          | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.57          | ~ (v1_relat_1 @ X1)
% 0.21/0.57          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.21/0.57             (k1_relat_1 @ X1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X0)
% 0.21/0.57          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.21/0.57          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | (v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.21/0.57          | ~ (v1_relat_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ (k9_relat_1 @ X0 @ X1))
% 0.21/0.57          | ~ (v1_relat_1 @ X0)
% 0.21/0.57          | ~ (v1_funct_1 @ X0)
% 0.21/0.57          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.57  thf(t116_funct_2, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.21/0.57              ( ![F:$i]:
% 0.21/0.57                ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.57                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.21/0.57                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.57          ( ![E:$i]:
% 0.21/0.57            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.21/0.57                 ( ![F:$i]:
% 0.21/0.57                   ( ( m1_subset_1 @ F @ A ) =>
% 0.21/0.57                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.21/0.57                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.21/0.57          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.21/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.21/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('19', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      ((~ (v1_xboole_0 @ sk_D_1)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.57        | ~ (v1_relat_1 @ sk_D_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '19'])).
% 0.21/0.57  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc1_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( v1_relat_1 @ C ) ))).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.57         ((v1_relat_1 @ X16)
% 0.21/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.57  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('25', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(cc3_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.57       ( ![C:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57           ( v1_xboole_0 @ C ) ) ) ))).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X21)))
% 0.21/0.57          | (v1_xboole_0 @ X20))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.21/0.57  thf('28', plain, (((v1_xboole_0 @ sk_D_1) | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.21/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('31', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t52_relset_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.21/0.57               ( ![D:$i]:
% 0.21/0.57                 ( ( m1_subset_1 @
% 0.21/0.57                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.21/0.57                   ( ![E:$i]:
% 0.21/0.57                     ( ( m1_subset_1 @ E @ A ) =>
% 0.21/0.57                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.21/0.57                         ( ?[F:$i]:
% 0.21/0.57                           ( ( r2_hidden @ F @ B ) & 
% 0.21/0.57                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.21/0.57                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.57          | ~ (r2_hidden @ X35 @ (k7_relset_1 @ X32 @ X33 @ X31 @ X30))
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_F @ X35 @ X31 @ X32 @ X30) @ X35) @ 
% 0.21/0.57             X31)
% 0.21/0.57          | ~ (m1_subset_1 @ X35 @ X33)
% 0.21/0.57          | (v1_xboole_0 @ X32)
% 0.21/0.57          | (v1_xboole_0 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.21/0.57             sk_D_1)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1))
% 0.21/0.57          | (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.21/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.21/0.57             sk_D_1)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.21/0.57          | (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | (r2_hidden @ 
% 0.21/0.57           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.21/0.57        | ~ (m1_subset_1 @ sk_E @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(dt_k7_relset_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.57       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.21/0.57          | (m1_subset_1 @ (k7_relset_1 @ X23 @ X24 @ X22 @ X25) @ 
% 0.21/0.57             (k1_zfmisc_1 @ X24)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0) @ 
% 0.21/0.57          (k1_zfmisc_1 @ sk_B_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf(t4_subset, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.21/0.57       ( m1_subset_1 @ A @ C ) ))).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X6 @ X7)
% 0.21/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.21/0.57          | (m1_subset_1 @ X6 @ X8))),
% 0.21/0.57      inference('cnf', [status(esa)], [t4_subset])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X1 @ sk_B_2)
% 0.21/0.57          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.57  thf('44', plain, ((m1_subset_1 @ sk_E @ sk_B_2)),
% 0.21/0.57      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.57  thf('45', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | (r2_hidden @ 
% 0.21/0.57           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_E) @ sk_D_1)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('demod', [status(thm)], ['37', '44'])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.21/0.57          | ((X15) = (k1_funct_1 @ X14 @ X13))
% 0.21/0.57          | ~ (v1_funct_1 @ X14)
% 0.21/0.57          | ~ (v1_relat_1 @ X14))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | ~ (v1_relat_1 @ sk_D_1)
% 0.21/0.57        | ~ (v1_funct_1 @ sk_D_1)
% 0.21/0.57        | ((sk_E)
% 0.21/0.57            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.57  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('49', plain, ((v1_funct_1 @ sk_D_1)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | ((sk_E)
% 0.21/0.57            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.21/0.57      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.21/0.57  thf('51', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.57          | ~ (r2_hidden @ X35 @ (k7_relset_1 @ X32 @ X33 @ X31 @ X30))
% 0.21/0.57          | (m1_subset_1 @ (sk_F @ X35 @ X31 @ X32 @ X30) @ X32)
% 0.21/0.57          | ~ (m1_subset_1 @ X35 @ X33)
% 0.21/0.57          | (v1_xboole_0 @ X32)
% 0.21/0.57          | (v1_xboole_0 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.57          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1))
% 0.21/0.57          | (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.21/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.57          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.21/0.57          | (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.57        | ~ (m1_subset_1 @ sk_E @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['51', '56'])).
% 0.21/0.57  thf('58', plain, ((m1_subset_1 @ sk_E @ sk_B_2)),
% 0.21/0.57      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X35 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.21/0.57          | ~ (r2_hidden @ X35 @ (k7_relset_1 @ X32 @ X33 @ X31 @ X30))
% 0.21/0.57          | (r2_hidden @ (sk_F @ X35 @ X31 @ X32 @ X30) @ X30)
% 0.21/0.57          | ~ (m1_subset_1 @ X35 @ X33)
% 0.21/0.57          | (v1_xboole_0 @ X32)
% 0.21/0.57          | (v1_xboole_0 @ X33))),
% 0.21/0.57      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.21/0.57  thf('63', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.57          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X1))
% 0.21/0.57          | (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.21/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ sk_A)
% 0.21/0.57          | ~ (m1_subset_1 @ X0 @ sk_B_2)
% 0.21/0.57          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.21/0.57          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.21/0.57          | (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('demod', [status(thm)], ['63', '64'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.21/0.57        | ~ (m1_subset_1 @ sk_E @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['60', '65'])).
% 0.21/0.57  thf('67', plain, ((m1_subset_1 @ sk_E @ sk_B_2)),
% 0.21/0.57      inference('sup-', [status(thm)], ['38', '43'])).
% 0.21/0.57  thf('68', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_C)
% 0.21/0.57        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_C)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('demod', [status(thm)], ['66', '67'])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      (![X36 : $i]:
% 0.21/0.57         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X36))
% 0.21/0.57          | ~ (r2_hidden @ X36 @ sk_C)
% 0.21/0.57          | ~ (m1_subset_1 @ X36 @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | ~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C) @ sk_A)
% 0.21/0.57        | ((sk_E)
% 0.21/0.57            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | ((sk_E)
% 0.21/0.57            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['59', '70'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C)))
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('simplify', [status(thm)], ['71'])).
% 0.21/0.57  thf('73', plain,
% 0.21/0.57      ((((sk_E) != (sk_E))
% 0.21/0.57        | (v1_xboole_0 @ sk_C)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_B_2)
% 0.21/0.57        | (v1_xboole_0 @ sk_A)
% 0.21/0.57        | (v1_xboole_0 @ sk_C))),
% 0.21/0.57      inference('sup-', [status(thm)], ['50', '72'])).
% 0.21/0.57  thf('74', plain,
% 0.21/0.57      (((v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.21/0.57      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.21/0.57          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.21/0.57          | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.57  thf('77', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.57          | ~ (v1_relat_1 @ X1)
% 0.21/0.57          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.21/0.57             X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ X1)
% 0.21/0.57          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.21/0.57          | ~ (v1_xboole_0 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['77', '78'])).
% 0.21/0.57  thf('80', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['15', '18'])).
% 0.21/0.57  thf('81', plain, ((~ (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_D_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('82', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('83', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.21/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.57  thf('84', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_2))),
% 0.21/0.57      inference('clc', [status(thm)], ['74', '83'])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0) @ 
% 0.21/0.57          (k1_zfmisc_1 @ sk_B_2))),
% 0.21/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf(cc1_subset_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( v1_xboole_0 @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.21/0.57          | (v1_xboole_0 @ X4)
% 0.21/0.57          | ~ (v1_xboole_0 @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ sk_B_2)
% 0.21/0.57          | (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.21/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_xboole_0 @ sk_B_2) | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.21/0.57      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['84', '89'])).
% 0.21/0.57  thf('91', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.21/0.57          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ (k1_relat_1 @ X12))
% 0.21/0.57          | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.57        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.57  thf('94', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.57  thf('96', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.21/0.57          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.21/0.57          | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.21/0.57        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.21/0.57           sk_D_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['96', '97'])).
% 0.21/0.57  thf('99', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('100', plain,
% 0.21/0.57      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['98', '99'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X9 @ X10)
% 0.21/0.57          | ~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X12)
% 0.21/0.57          | ~ (r2_hidden @ X9 @ (k1_relat_1 @ X12))
% 0.21/0.57          | (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.21/0.57          | ~ (v1_relat_1 @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_relat_1 @ sk_D_1)
% 0.21/0.57          | (r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ 
% 0.21/0.57               (k1_relat_1 @ sk_D_1))
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['100', '101'])).
% 0.21/0.57  thf('103', plain, ((v1_relat_1 @ sk_D_1)),
% 0.21/0.57      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.21/0.57      inference('demod', [status(thm)], ['93', '94'])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ X0))),
% 0.21/0.57      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['95', '105'])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.21/0.57  thf('109', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.57      inference('sup-', [status(thm)], ['90', '108'])).
% 0.21/0.57  thf('110', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.21/0.57      inference('demod', [status(thm)], ['28', '109'])).
% 0.21/0.57  thf('111', plain, ($false), inference('demod', [status(thm)], ['25', '110'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
