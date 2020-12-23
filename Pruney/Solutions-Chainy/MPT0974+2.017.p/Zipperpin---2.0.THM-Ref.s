%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eizi21EjR2

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:42 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 140 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   12
%              Number of atoms          :  738 (2582 expanded)
%              Number of equality atoms :   41 ( 179 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X7 @ X6 ) )
        = ( k9_relat_1 @ X6 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t20_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( ( k2_relset_1 @ B @ C @ E )
                = C ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ D )
                  = B )
                & ( ( k2_relset_1 @ B @ C @ E )
                  = C ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_funct_2])).

thf('1',plain,(
    ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ( k2_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('16',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
 != sk_C ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
     != sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['0','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k7_relat_1 @ X8 @ X9 ) )
      | ~ ( v4_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['34','39'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('42',plain,
    ( ( ( k2_relat_1 @ sk_E )
      = ( k9_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['37','38'])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_E )
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('47',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k2_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_E )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( sk_C
    = ( k9_relat_1 @ sk_E @ sk_B ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['37','38'])).

thf('57',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['24','29','50','55','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eizi21EjR2
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.42/0.59  % Solved by: fo/fo7.sh
% 0.42/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.59  % done 165 iterations in 0.144s
% 0.42/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.42/0.59  % SZS output start Refutation
% 0.42/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.59  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.59  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.59  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.59  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.42/0.59  thf(t160_relat_1, axiom,
% 0.42/0.59    (![A:$i]:
% 0.42/0.59     ( ( v1_relat_1 @ A ) =>
% 0.42/0.59       ( ![B:$i]:
% 0.42/0.59         ( ( v1_relat_1 @ B ) =>
% 0.42/0.59           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.42/0.59             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.42/0.59  thf('0', plain,
% 0.42/0.59      (![X6 : $i, X7 : $i]:
% 0.42/0.59         (~ (v1_relat_1 @ X6)
% 0.42/0.59          | ((k2_relat_1 @ (k5_relat_1 @ X7 @ X6))
% 0.42/0.59              = (k9_relat_1 @ X6 @ (k2_relat_1 @ X7)))
% 0.42/0.59          | ~ (v1_relat_1 @ X7))),
% 0.42/0.59      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.42/0.59  thf(t20_funct_2, conjecture,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59       ( ![E:$i]:
% 0.42/0.59         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.42/0.59             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.42/0.59           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.42/0.59               ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.42/0.59             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59               ( ( k2_relset_1 @
% 0.42/0.59                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.42/0.59                 ( C ) ) ) ) ) ) ))).
% 0.42/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.42/0.59            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.59          ( ![E:$i]:
% 0.42/0.59            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.42/0.59                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.42/0.59              ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 0.42/0.59                  ( ( k2_relset_1 @ B @ C @ E ) = ( C ) ) ) =>
% 0.42/0.59                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.42/0.59                  ( ( k2_relset_1 @
% 0.42/0.59                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 0.42/0.59                    ( C ) ) ) ) ) ) ) )),
% 0.42/0.59    inference('cnf.neg', [status(esa)], [t20_funct_2])).
% 0.42/0.59  thf('1', plain,
% 0.42/0.59      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.42/0.59         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) != (sk_C))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('2', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('3', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(dt_k1_partfun1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.42/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.42/0.59         ( v1_funct_1 @ F ) & 
% 0.42/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.42/0.59       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.42/0.59         ( m1_subset_1 @
% 0.42/0.59           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.59           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.42/0.59  thf('4', plain,
% 0.42/0.59      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.42/0.59          | ~ (v1_funct_1 @ X16)
% 0.42/0.59          | ~ (v1_funct_1 @ X19)
% 0.42/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.42/0.59          | (m1_subset_1 @ (k1_partfun1 @ X17 @ X18 @ X20 @ X21 @ X16 @ X19) @ 
% 0.42/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X21))))),
% 0.42/0.59      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.42/0.59  thf('5', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.42/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.42/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.42/0.59          | ~ (v1_funct_1 @ X1)
% 0.42/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.42/0.59  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('7', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 0.42/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.42/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.42/0.59          | ~ (v1_funct_1 @ X1))),
% 0.42/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.42/0.59  thf('8', plain,
% 0.42/0.59      ((~ (v1_funct_1 @ sk_E)
% 0.42/0.59        | (m1_subset_1 @ 
% 0.42/0.59           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.42/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.42/0.59      inference('sup-', [status(thm)], ['2', '7'])).
% 0.42/0.59  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('10', plain,
% 0.42/0.59      ((m1_subset_1 @ 
% 0.42/0.59        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 0.42/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.42/0.59      inference('demod', [status(thm)], ['8', '9'])).
% 0.42/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i]:
% 0.42/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.59  thf('11', plain,
% 0.42/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.59         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.42/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.59  thf('12', plain,
% 0.42/0.59      (((k2_relset_1 @ sk_A @ sk_C @ 
% 0.42/0.59         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.42/0.59         = (k2_relat_1 @ 
% 0.42/0.59            (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.59  thf('13', plain,
% 0.42/0.59      (((k2_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E))
% 0.42/0.59         != (sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['1', '12'])).
% 0.42/0.59  thf('14', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('15', plain,
% 0.42/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf(redefinition_k1_partfun1, axiom,
% 0.42/0.59    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.59     ( ( ( v1_funct_1 @ E ) & 
% 0.42/0.59         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.42/0.59         ( v1_funct_1 @ F ) & 
% 0.42/0.59         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.42/0.59       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.42/0.59  thf('16', plain,
% 0.42/0.59      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.42/0.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.42/0.59          | ~ (v1_funct_1 @ X22)
% 0.42/0.59          | ~ (v1_funct_1 @ X25)
% 0.42/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.42/0.59          | ((k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.42/0.59              = (k5_relat_1 @ X22 @ X25)))),
% 0.42/0.59      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.42/0.59  thf('17', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.42/0.59            = (k5_relat_1 @ sk_D @ X0))
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.42/0.59          | ~ (v1_funct_1 @ X0)
% 0.42/0.59          | ~ (v1_funct_1 @ sk_D))),
% 0.42/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.59  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('19', plain,
% 0.42/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.59         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 0.42/0.59            = (k5_relat_1 @ sk_D @ X0))
% 0.42/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.42/0.59          | ~ (v1_funct_1 @ X0))),
% 0.42/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.59  thf('20', plain,
% 0.42/0.59      ((~ (v1_funct_1 @ sk_E)
% 0.42/0.59        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.42/0.59            = (k5_relat_1 @ sk_D @ sk_E)))),
% 0.42/0.59      inference('sup-', [status(thm)], ['14', '19'])).
% 0.42/0.59  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.59  thf('22', plain,
% 0.42/0.59      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 0.42/0.59         = (k5_relat_1 @ sk_D @ sk_E))),
% 0.42/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.42/0.59  thf('23', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) != (sk_C))),
% 0.42/0.59      inference('demod', [status(thm)], ['13', '22'])).
% 0.42/0.60  thf('24', plain,
% 0.42/0.60      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) != (sk_C))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.42/0.60        | ~ (v1_relat_1 @ sk_E))),
% 0.42/0.60      inference('sup-', [status(thm)], ['0', '23'])).
% 0.42/0.60  thf('25', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('26', plain,
% 0.42/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.60         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.42/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.60  thf('27', plain,
% 0.42/0.60      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.42/0.60  thf('28', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (sk_B))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 0.42/0.60      inference('sup+', [status(thm)], ['27', '28'])).
% 0.42/0.60  thf('30', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relset_1, axiom,
% 0.42/0.60    (![A:$i,B:$i,C:$i]:
% 0.42/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.60  thf('31', plain,
% 0.42/0.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.60         ((v4_relat_1 @ X10 @ X11)
% 0.42/0.60          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.60  thf('32', plain, ((v4_relat_1 @ sk_E @ sk_B)),
% 0.42/0.60      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.60  thf(t209_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.42/0.60       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.42/0.60  thf('33', plain,
% 0.42/0.60      (![X8 : $i, X9 : $i]:
% 0.42/0.60         (((X8) = (k7_relat_1 @ X8 @ X9))
% 0.42/0.60          | ~ (v4_relat_1 @ X8 @ X9)
% 0.42/0.60          | ~ (v1_relat_1 @ X8))),
% 0.42/0.60      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.42/0.60  thf('34', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_B)))),
% 0.42/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.60  thf('35', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf(cc2_relat_1, axiom,
% 0.42/0.60    (![A:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ A ) =>
% 0.42/0.60       ( ![B:$i]:
% 0.42/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.60  thf('36', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.60          | (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.60  thf('37', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_E))),
% 0.42/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.42/0.60  thf(fc6_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.60  thf('38', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.60  thf('39', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('40', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['34', '39'])).
% 0.42/0.60  thf(t148_relat_1, axiom,
% 0.42/0.60    (![A:$i,B:$i]:
% 0.42/0.60     ( ( v1_relat_1 @ B ) =>
% 0.42/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.42/0.60  thf('41', plain,
% 0.42/0.60      (![X4 : $i, X5 : $i]:
% 0.42/0.60         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.42/0.60          | ~ (v1_relat_1 @ X4))),
% 0.42/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.42/0.60  thf('42', plain,
% 0.42/0.60      ((((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))
% 0.42/0.60        | ~ (v1_relat_1 @ sk_E))),
% 0.42/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.42/0.60  thf('43', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('44', plain, (((k2_relat_1 @ sk_E) = (k9_relat_1 @ sk_E @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.60  thf('45', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('46', plain,
% 0.42/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.42/0.60         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.42/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.42/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.60  thf('47', plain,
% 0.42/0.60      (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (k2_relat_1 @ sk_E))),
% 0.42/0.60      inference('sup-', [status(thm)], ['45', '46'])).
% 0.42/0.60  thf('48', plain, (((k2_relset_1 @ sk_B @ sk_C @ sk_E) = (sk_C))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('49', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 0.42/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.60  thf('50', plain, (((sk_C) = (k9_relat_1 @ sk_E @ sk_B))),
% 0.42/0.60      inference('demod', [status(thm)], ['44', '49'])).
% 0.42/0.60  thf('51', plain,
% 0.42/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.60  thf('52', plain,
% 0.42/0.60      (![X0 : $i, X1 : $i]:
% 0.42/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.60          | (v1_relat_1 @ X0)
% 0.42/0.60          | ~ (v1_relat_1 @ X1))),
% 0.42/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.60  thf('53', plain,
% 0.42/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.42/0.60      inference('sup-', [status(thm)], ['51', '52'])).
% 0.42/0.60  thf('54', plain,
% 0.42/0.60      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.42/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.60  thf('55', plain, ((v1_relat_1 @ sk_D)),
% 0.42/0.60      inference('demod', [status(thm)], ['53', '54'])).
% 0.42/0.60  thf('56', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.60      inference('demod', [status(thm)], ['37', '38'])).
% 0.42/0.60  thf('57', plain, (((sk_C) != (sk_C))),
% 0.42/0.60      inference('demod', [status(thm)], ['24', '29', '50', '55', '56'])).
% 0.42/0.60  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.42/0.60  
% 0.42/0.60  % SZS output end Refutation
% 0.42/0.60  
% 0.42/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
