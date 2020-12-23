%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1KxNckbuRN

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:57 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 621 expanded)
%              Number of leaves         :   45 ( 199 expanded)
%              Depth                    :   15
%              Number of atoms          : 1088 (14228 expanded)
%              Number of equality atoms :   65 ( 822 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) )
        = ( k9_relat_1 @ X5 @ ( k2_relat_1 @ X6 ) ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf(t28_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                = C )
              & ( v2_funct_1 @ E ) )
           => ( ( C = k1_xboole_0 )
              | ( ( k2_relset_1 @ A @ B @ D )
                = B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ B @ C )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
                  = C )
                & ( v2_funct_1 @ E ) )
             => ( ( C = k1_xboole_0 )
                | ( ( k2_relset_1 @ A @ B @ D )
                  = B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
      = ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8','17'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E ) )
    = sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E )
    = ( k5_relat_1 @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,
    ( ( k2_relset_1 @ sk_A @ sk_C @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['0','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('31',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','28','31'])).

thf(t152_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( r1_tarski @ ( k10_relat_1 @ X10 @ ( k9_relat_1 @ X10 @ X11 ) ) @ X11 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t152_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) )
      | ( X0
        = ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k10_relat_1 @ sk_E @ sk_C ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k10_relat_1 @ sk_E @ ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v2_funct_1 @ sk_E )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['20','23'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X9 @ X8 ) ) @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C )
    | ( ( k2_relat_1 @ sk_E )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) ) )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    v5_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['29','30'])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ sk_E ) )
    = sk_C ),
    inference('sup+',[status(thm)],['20','23'])).

thf('50',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['29','30'])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['41','48','49','50','51'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('53',plain,(
    ! [X7: $i] :
      ( ( ( k10_relat_1 @ X7 @ ( k2_relat_1 @ X7 ) )
        = ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('54',plain,
    ( ( ( k10_relat_1 @ sk_E @ sk_C )
      = ( k1_relat_1 @ sk_E ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_funct_2 @ sk_E @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_E ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('61',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_E @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    zip_tseitin_1 @ sk_E @ sk_C @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('66',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('67',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['57','64','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['29','30'])).

thf('70',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['54','68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('73',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v5_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k2_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('75',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['26','27'])).

thf('77',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k9_relat_1 @ sk_E @ ( k2_relat_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['25','28','31'])).

thf('79',plain,
    ( ( k10_relat_1 @ sk_E @ sk_C )
    = sk_B ),
    inference(demod,[status(thm)],['54','68','69'])).

thf('80',plain,(
    v2_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['29','30'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['36','70','77','78','79','80','81','82'])).

thf('84',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('87',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ( k2_relat_1 @ sk_D )
 != sk_B ),
    inference(demod,[status(thm)],['84','87'])).

thf('89',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['83','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1KxNckbuRN
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:42:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.50/1.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.50/1.75  % Solved by: fo/fo7.sh
% 1.50/1.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.50/1.75  % done 673 iterations in 1.297s
% 1.50/1.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.50/1.75  % SZS output start Refutation
% 1.50/1.75  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.50/1.75  thf(sk_C_type, type, sk_C: $i).
% 1.50/1.75  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.50/1.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.50/1.75  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.50/1.75  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.50/1.75  thf(sk_B_type, type, sk_B: $i).
% 1.50/1.75  thf(sk_E_type, type, sk_E: $i).
% 1.50/1.75  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.50/1.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.50/1.75  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.50/1.75  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.50/1.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.50/1.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.50/1.75  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.50/1.75  thf(sk_D_type, type, sk_D: $i).
% 1.50/1.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.50/1.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.50/1.75  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.50/1.75  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.50/1.75  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.50/1.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.50/1.75  thf(sk_A_type, type, sk_A: $i).
% 1.50/1.75  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.50/1.75  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.50/1.75  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.50/1.75  thf(t160_relat_1, axiom,
% 1.50/1.75    (![A:$i]:
% 1.50/1.75     ( ( v1_relat_1 @ A ) =>
% 1.50/1.75       ( ![B:$i]:
% 1.50/1.75         ( ( v1_relat_1 @ B ) =>
% 1.50/1.75           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.50/1.75             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.50/1.75  thf('0', plain,
% 1.50/1.75      (![X5 : $i, X6 : $i]:
% 1.50/1.75         (~ (v1_relat_1 @ X5)
% 1.50/1.75          | ((k2_relat_1 @ (k5_relat_1 @ X6 @ X5))
% 1.50/1.75              = (k9_relat_1 @ X5 @ (k2_relat_1 @ X6)))
% 1.50/1.75          | ~ (v1_relat_1 @ X6))),
% 1.50/1.75      inference('cnf', [status(esa)], [t160_relat_1])).
% 1.50/1.75  thf(t28_funct_2, conjecture,
% 1.50/1.75    (![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.75     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.50/1.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.50/1.75       ( ![E:$i]:
% 1.50/1.75         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.50/1.75             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.50/1.75           ( ( ( ( k2_relset_1 @
% 1.50/1.75                   A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.50/1.75                 ( C ) ) & 
% 1.50/1.75               ( v2_funct_1 @ E ) ) =>
% 1.50/1.75             ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.50/1.75               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ))).
% 1.50/1.75  thf(zf_stmt_0, negated_conjecture,
% 1.50/1.75    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.50/1.75        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.50/1.75            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.50/1.75          ( ![E:$i]:
% 1.50/1.75            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.50/1.75                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.50/1.75              ( ( ( ( k2_relset_1 @
% 1.50/1.75                      A @ C @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =
% 1.50/1.75                    ( C ) ) & 
% 1.50/1.75                  ( v2_funct_1 @ E ) ) =>
% 1.50/1.75                ( ( ( C ) = ( k1_xboole_0 ) ) | 
% 1.50/1.75                  ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) ) ) ) ) )),
% 1.50/1.75    inference('cnf.neg', [status(esa)], [t28_funct_2])).
% 1.50/1.75  thf('1', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('2', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(dt_k1_partfun1, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.50/1.75     ( ( ( v1_funct_1 @ E ) & 
% 1.50/1.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.50/1.75         ( v1_funct_1 @ F ) & 
% 1.50/1.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.50/1.75       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.50/1.75         ( m1_subset_1 @
% 1.50/1.75           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.50/1.75           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.50/1.75  thf('3', plain,
% 1.50/1.75      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.50/1.75         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 1.50/1.75          | ~ (v1_funct_1 @ X32)
% 1.50/1.75          | ~ (v1_funct_1 @ X35)
% 1.50/1.75          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.50/1.75          | (m1_subset_1 @ (k1_partfun1 @ X33 @ X34 @ X36 @ X37 @ X32 @ X35) @ 
% 1.50/1.75             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X37))))),
% 1.50/1.75      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.50/1.75  thf('4', plain,
% 1.50/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.50/1.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.50/1.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.50/1.75          | ~ (v1_funct_1 @ X1)
% 1.50/1.75          | ~ (v1_funct_1 @ sk_D))),
% 1.50/1.75      inference('sup-', [status(thm)], ['2', '3'])).
% 1.50/1.75  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('6', plain,
% 1.50/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.75         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_D @ X1) @ 
% 1.50/1.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.50/1.75          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.50/1.75          | ~ (v1_funct_1 @ X1))),
% 1.50/1.75      inference('demod', [status(thm)], ['4', '5'])).
% 1.50/1.75  thf('7', plain,
% 1.50/1.75      ((~ (v1_funct_1 @ sk_E)
% 1.50/1.75        | (m1_subset_1 @ 
% 1.50/1.75           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E) @ 
% 1.50/1.75           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 1.50/1.75      inference('sup-', [status(thm)], ['1', '6'])).
% 1.50/1.75  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('9', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('10', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(redefinition_k1_partfun1, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.50/1.75     ( ( ( v1_funct_1 @ E ) & 
% 1.50/1.75         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.50/1.75         ( v1_funct_1 @ F ) & 
% 1.50/1.75         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.50/1.75       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.50/1.75  thf('11', plain,
% 1.50/1.75      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.50/1.75         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.50/1.75          | ~ (v1_funct_1 @ X38)
% 1.50/1.75          | ~ (v1_funct_1 @ X41)
% 1.50/1.75          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 1.50/1.75          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 1.50/1.75              = (k5_relat_1 @ X38 @ X41)))),
% 1.50/1.75      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.50/1.75  thf('12', plain,
% 1.50/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.50/1.75            = (k5_relat_1 @ sk_D @ X0))
% 1.50/1.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.50/1.75          | ~ (v1_funct_1 @ X0)
% 1.50/1.75          | ~ (v1_funct_1 @ sk_D))),
% 1.50/1.75      inference('sup-', [status(thm)], ['10', '11'])).
% 1.50/1.75  thf('13', plain, ((v1_funct_1 @ sk_D)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('14', plain,
% 1.50/1.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.50/1.75         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_D @ X0)
% 1.50/1.75            = (k5_relat_1 @ sk_D @ X0))
% 1.50/1.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.50/1.75          | ~ (v1_funct_1 @ X0))),
% 1.50/1.75      inference('demod', [status(thm)], ['12', '13'])).
% 1.50/1.75  thf('15', plain,
% 1.50/1.75      ((~ (v1_funct_1 @ sk_E)
% 1.50/1.75        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.50/1.75            = (k5_relat_1 @ sk_D @ sk_E)))),
% 1.50/1.75      inference('sup-', [status(thm)], ['9', '14'])).
% 1.50/1.75  thf('16', plain, ((v1_funct_1 @ sk_E)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('17', plain,
% 1.50/1.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.50/1.75         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.50/1.75      inference('demod', [status(thm)], ['15', '16'])).
% 1.50/1.75  thf('18', plain,
% 1.50/1.75      ((m1_subset_1 @ (k5_relat_1 @ sk_D @ sk_E) @ 
% 1.50/1.75        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 1.50/1.75      inference('demod', [status(thm)], ['7', '8', '17'])).
% 1.50/1.75  thf(redefinition_k2_relset_1, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i]:
% 1.50/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.75       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.50/1.75  thf('19', plain,
% 1.50/1.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.75         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.50/1.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.50/1.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.50/1.75  thf('20', plain,
% 1.50/1.75      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E))
% 1.50/1.75         = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))),
% 1.50/1.75      inference('sup-', [status(thm)], ['18', '19'])).
% 1.50/1.75  thf('21', plain,
% 1.50/1.75      (((k2_relset_1 @ sk_A @ sk_C @ 
% 1.50/1.75         (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)) = (sk_C))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('22', plain,
% 1.50/1.75      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_C @ sk_D @ sk_E)
% 1.50/1.75         = (k5_relat_1 @ sk_D @ sk_E))),
% 1.50/1.75      inference('demod', [status(thm)], ['15', '16'])).
% 1.50/1.75  thf('23', plain,
% 1.50/1.75      (((k2_relset_1 @ sk_A @ sk_C @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.50/1.75      inference('demod', [status(thm)], ['21', '22'])).
% 1.50/1.75  thf('24', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.50/1.75      inference('sup+', [status(thm)], ['20', '23'])).
% 1.50/1.75  thf('25', plain,
% 1.50/1.75      ((((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))
% 1.50/1.75        | ~ (v1_relat_1 @ sk_D)
% 1.50/1.75        | ~ (v1_relat_1 @ sk_E))),
% 1.50/1.75      inference('sup+', [status(thm)], ['0', '24'])).
% 1.50/1.75  thf('26', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(cc1_relset_1, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i]:
% 1.50/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.75       ( v1_relat_1 @ C ) ))).
% 1.50/1.75  thf('27', plain,
% 1.50/1.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.50/1.75         ((v1_relat_1 @ X12)
% 1.50/1.75          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.50/1.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.50/1.75  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.75      inference('sup-', [status(thm)], ['26', '27'])).
% 1.50/1.75  thf('29', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('30', plain,
% 1.50/1.75      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.50/1.75         ((v1_relat_1 @ X12)
% 1.50/1.75          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.50/1.75      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.50/1.75  thf('31', plain, ((v1_relat_1 @ sk_E)),
% 1.50/1.75      inference('sup-', [status(thm)], ['29', '30'])).
% 1.50/1.75  thf('32', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 1.50/1.75      inference('demod', [status(thm)], ['25', '28', '31'])).
% 1.50/1.75  thf(t152_funct_1, axiom,
% 1.50/1.75    (![A:$i,B:$i]:
% 1.50/1.75     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.50/1.75       ( ( v2_funct_1 @ B ) =>
% 1.50/1.75         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 1.50/1.75  thf('33', plain,
% 1.50/1.75      (![X10 : $i, X11 : $i]:
% 1.50/1.75         (~ (v2_funct_1 @ X10)
% 1.50/1.75          | (r1_tarski @ (k10_relat_1 @ X10 @ (k9_relat_1 @ X10 @ X11)) @ X11)
% 1.50/1.75          | ~ (v1_funct_1 @ X10)
% 1.50/1.75          | ~ (v1_relat_1 @ X10))),
% 1.50/1.75      inference('cnf', [status(esa)], [t152_funct_1])).
% 1.50/1.75  thf(d10_xboole_0, axiom,
% 1.50/1.75    (![A:$i,B:$i]:
% 1.50/1.75     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.50/1.75  thf('34', plain,
% 1.50/1.75      (![X0 : $i, X2 : $i]:
% 1.50/1.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.75  thf('35', plain,
% 1.50/1.75      (![X0 : $i, X1 : $i]:
% 1.50/1.75         (~ (v1_relat_1 @ X1)
% 1.50/1.75          | ~ (v1_funct_1 @ X1)
% 1.50/1.75          | ~ (v2_funct_1 @ X1)
% 1.50/1.75          | ~ (r1_tarski @ X0 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)))
% 1.50/1.75          | ((X0) = (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0))))),
% 1.50/1.75      inference('sup-', [status(thm)], ['33', '34'])).
% 1.50/1.75  thf('36', plain,
% 1.50/1.75      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k10_relat_1 @ sk_E @ sk_C))
% 1.50/1.75        | ((k2_relat_1 @ sk_D)
% 1.50/1.75            = (k10_relat_1 @ sk_E @ (k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D))))
% 1.50/1.75        | ~ (v2_funct_1 @ sk_E)
% 1.50/1.75        | ~ (v1_funct_1 @ sk_E)
% 1.50/1.75        | ~ (v1_relat_1 @ sk_E))),
% 1.50/1.75      inference('sup-', [status(thm)], ['32', '35'])).
% 1.50/1.75  thf('37', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.50/1.75      inference('sup+', [status(thm)], ['20', '23'])).
% 1.50/1.75  thf(t45_relat_1, axiom,
% 1.50/1.75    (![A:$i]:
% 1.50/1.75     ( ( v1_relat_1 @ A ) =>
% 1.50/1.75       ( ![B:$i]:
% 1.50/1.75         ( ( v1_relat_1 @ B ) =>
% 1.50/1.75           ( r1_tarski @
% 1.50/1.75             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.50/1.75  thf('38', plain,
% 1.50/1.75      (![X8 : $i, X9 : $i]:
% 1.50/1.75         (~ (v1_relat_1 @ X8)
% 1.50/1.75          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X9 @ X8)) @ 
% 1.50/1.75             (k2_relat_1 @ X8))
% 1.50/1.75          | ~ (v1_relat_1 @ X9))),
% 1.50/1.75      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.50/1.75  thf('39', plain,
% 1.50/1.75      (![X0 : $i, X2 : $i]:
% 1.50/1.75         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.50/1.75      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.50/1.75  thf('40', plain,
% 1.50/1.75      (![X0 : $i, X1 : $i]:
% 1.50/1.75         (~ (v1_relat_1 @ X1)
% 1.50/1.75          | ~ (v1_relat_1 @ X0)
% 1.50/1.75          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ 
% 1.50/1.75               (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.50/1.75          | ((k2_relat_1 @ X0) = (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.50/1.75      inference('sup-', [status(thm)], ['38', '39'])).
% 1.50/1.75  thf('41', plain,
% 1.50/1.75      ((~ (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)
% 1.50/1.75        | ((k2_relat_1 @ sk_E) = (k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)))
% 1.50/1.75        | ~ (v1_relat_1 @ sk_E)
% 1.50/1.75        | ~ (v1_relat_1 @ sk_D))),
% 1.50/1.75      inference('sup-', [status(thm)], ['37', '40'])).
% 1.50/1.75  thf('42', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(cc2_relset_1, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i]:
% 1.50/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.75       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.50/1.75  thf('43', plain,
% 1.50/1.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.50/1.75         ((v5_relat_1 @ X15 @ X17)
% 1.50/1.75          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.50/1.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.75  thf('44', plain, ((v5_relat_1 @ sk_E @ sk_C)),
% 1.50/1.75      inference('sup-', [status(thm)], ['42', '43'])).
% 1.50/1.75  thf(d19_relat_1, axiom,
% 1.50/1.75    (![A:$i,B:$i]:
% 1.50/1.75     ( ( v1_relat_1 @ B ) =>
% 1.50/1.75       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 1.50/1.75  thf('45', plain,
% 1.50/1.75      (![X3 : $i, X4 : $i]:
% 1.50/1.75         (~ (v5_relat_1 @ X3 @ X4)
% 1.50/1.75          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.50/1.75          | ~ (v1_relat_1 @ X3))),
% 1.50/1.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.50/1.75  thf('46', plain,
% 1.50/1.75      ((~ (v1_relat_1 @ sk_E) | (r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C))),
% 1.50/1.75      inference('sup-', [status(thm)], ['44', '45'])).
% 1.50/1.75  thf('47', plain, ((v1_relat_1 @ sk_E)),
% 1.50/1.75      inference('sup-', [status(thm)], ['29', '30'])).
% 1.50/1.75  thf('48', plain, ((r1_tarski @ (k2_relat_1 @ sk_E) @ sk_C)),
% 1.50/1.75      inference('demod', [status(thm)], ['46', '47'])).
% 1.50/1.75  thf('49', plain, (((k2_relat_1 @ (k5_relat_1 @ sk_D @ sk_E)) = (sk_C))),
% 1.50/1.75      inference('sup+', [status(thm)], ['20', '23'])).
% 1.50/1.75  thf('50', plain, ((v1_relat_1 @ sk_E)),
% 1.50/1.75      inference('sup-', [status(thm)], ['29', '30'])).
% 1.50/1.75  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.75      inference('sup-', [status(thm)], ['26', '27'])).
% 1.50/1.75  thf('52', plain, (((k2_relat_1 @ sk_E) = (sk_C))),
% 1.50/1.75      inference('demod', [status(thm)], ['41', '48', '49', '50', '51'])).
% 1.50/1.75  thf(t169_relat_1, axiom,
% 1.50/1.75    (![A:$i]:
% 1.50/1.75     ( ( v1_relat_1 @ A ) =>
% 1.50/1.75       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 1.50/1.75  thf('53', plain,
% 1.50/1.75      (![X7 : $i]:
% 1.50/1.75         (((k10_relat_1 @ X7 @ (k2_relat_1 @ X7)) = (k1_relat_1 @ X7))
% 1.50/1.75          | ~ (v1_relat_1 @ X7))),
% 1.50/1.75      inference('cnf', [status(esa)], [t169_relat_1])).
% 1.50/1.75  thf('54', plain,
% 1.50/1.75      ((((k10_relat_1 @ sk_E @ sk_C) = (k1_relat_1 @ sk_E))
% 1.50/1.75        | ~ (v1_relat_1 @ sk_E))),
% 1.50/1.75      inference('sup+', [status(thm)], ['52', '53'])).
% 1.50/1.75  thf('55', plain, ((v1_funct_2 @ sk_E @ sk_B @ sk_C)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(d1_funct_2, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i]:
% 1.50/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.75       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.50/1.75           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.50/1.75             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.50/1.75         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.50/1.75           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.50/1.75             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.50/1.75  thf(zf_stmt_1, axiom,
% 1.50/1.75    (![C:$i,B:$i,A:$i]:
% 1.50/1.75     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.50/1.75       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.50/1.75  thf('56', plain,
% 1.50/1.75      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.50/1.75         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.50/1.75          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.50/1.75          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.50/1.75  thf('57', plain,
% 1.50/1.75      ((~ (zip_tseitin_1 @ sk_E @ sk_C @ sk_B)
% 1.50/1.75        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_E)))),
% 1.50/1.75      inference('sup-', [status(thm)], ['55', '56'])).
% 1.50/1.75  thf(zf_stmt_2, axiom,
% 1.50/1.75    (![B:$i,A:$i]:
% 1.50/1.75     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.50/1.75       ( zip_tseitin_0 @ B @ A ) ))).
% 1.50/1.75  thf('58', plain,
% 1.50/1.75      (![X24 : $i, X25 : $i]:
% 1.50/1.75         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.50/1.75  thf('59', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.50/1.75  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.50/1.75  thf(zf_stmt_5, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i]:
% 1.50/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.75       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.50/1.75         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.50/1.75           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.50/1.75             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.50/1.75  thf('60', plain,
% 1.50/1.75      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.50/1.75         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.50/1.75          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.50/1.75          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.50/1.75  thf('61', plain,
% 1.50/1.75      (((zip_tseitin_1 @ sk_E @ sk_C @ sk_B) | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.50/1.75      inference('sup-', [status(thm)], ['59', '60'])).
% 1.50/1.75  thf('62', plain,
% 1.50/1.75      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_E @ sk_C @ sk_B))),
% 1.50/1.75      inference('sup-', [status(thm)], ['58', '61'])).
% 1.50/1.75  thf('63', plain, (((sk_C) != (k1_xboole_0))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('64', plain, ((zip_tseitin_1 @ sk_E @ sk_C @ sk_B)),
% 1.50/1.75      inference('simplify_reflect-', [status(thm)], ['62', '63'])).
% 1.50/1.75  thf('65', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf(redefinition_k1_relset_1, axiom,
% 1.50/1.75    (![A:$i,B:$i,C:$i]:
% 1.50/1.75     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.50/1.75       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.50/1.75  thf('66', plain,
% 1.50/1.75      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.50/1.75         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 1.50/1.75          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.50/1.75      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.50/1.75  thf('67', plain,
% 1.50/1.75      (((k1_relset_1 @ sk_B @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 1.50/1.75      inference('sup-', [status(thm)], ['65', '66'])).
% 1.50/1.75  thf('68', plain, (((sk_B) = (k1_relat_1 @ sk_E))),
% 1.50/1.75      inference('demod', [status(thm)], ['57', '64', '67'])).
% 1.50/1.75  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 1.50/1.75      inference('sup-', [status(thm)], ['29', '30'])).
% 1.50/1.75  thf('70', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 1.50/1.75      inference('demod', [status(thm)], ['54', '68', '69'])).
% 1.50/1.75  thf('71', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('72', plain,
% 1.50/1.75      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.50/1.75         ((v5_relat_1 @ X15 @ X17)
% 1.50/1.75          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.50/1.75      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.50/1.75  thf('73', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 1.50/1.75      inference('sup-', [status(thm)], ['71', '72'])).
% 1.50/1.75  thf('74', plain,
% 1.50/1.75      (![X3 : $i, X4 : $i]:
% 1.50/1.75         (~ (v5_relat_1 @ X3 @ X4)
% 1.50/1.75          | (r1_tarski @ (k2_relat_1 @ X3) @ X4)
% 1.50/1.75          | ~ (v1_relat_1 @ X3))),
% 1.50/1.75      inference('cnf', [status(esa)], [d19_relat_1])).
% 1.50/1.75  thf('75', plain,
% 1.50/1.75      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 1.50/1.75      inference('sup-', [status(thm)], ['73', '74'])).
% 1.50/1.75  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 1.50/1.75      inference('sup-', [status(thm)], ['26', '27'])).
% 1.50/1.75  thf('77', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 1.50/1.75      inference('demod', [status(thm)], ['75', '76'])).
% 1.50/1.75  thf('78', plain, (((k9_relat_1 @ sk_E @ (k2_relat_1 @ sk_D)) = (sk_C))),
% 1.50/1.75      inference('demod', [status(thm)], ['25', '28', '31'])).
% 1.50/1.75  thf('79', plain, (((k10_relat_1 @ sk_E @ sk_C) = (sk_B))),
% 1.50/1.75      inference('demod', [status(thm)], ['54', '68', '69'])).
% 1.50/1.75  thf('80', plain, ((v2_funct_1 @ sk_E)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('81', plain, ((v1_funct_1 @ sk_E)),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('82', plain, ((v1_relat_1 @ sk_E)),
% 1.50/1.75      inference('sup-', [status(thm)], ['29', '30'])).
% 1.50/1.75  thf('83', plain, (((k2_relat_1 @ sk_D) = (sk_B))),
% 1.50/1.75      inference('demod', [status(thm)],
% 1.50/1.75                ['36', '70', '77', '78', '79', '80', '81', '82'])).
% 1.50/1.75  thf('84', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) != (sk_B))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('85', plain,
% 1.50/1.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.50/1.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.50/1.75  thf('86', plain,
% 1.50/1.75      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.50/1.75         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 1.50/1.75          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.50/1.75      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.50/1.75  thf('87', plain,
% 1.50/1.75      (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.50/1.75      inference('sup-', [status(thm)], ['85', '86'])).
% 1.50/1.75  thf('88', plain, (((k2_relat_1 @ sk_D) != (sk_B))),
% 1.50/1.75      inference('demod', [status(thm)], ['84', '87'])).
% 1.50/1.75  thf('89', plain, ($false),
% 1.50/1.75      inference('simplify_reflect-', [status(thm)], ['83', '88'])).
% 1.50/1.75  
% 1.50/1.75  % SZS output end Refutation
% 1.50/1.75  
% 1.50/1.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
