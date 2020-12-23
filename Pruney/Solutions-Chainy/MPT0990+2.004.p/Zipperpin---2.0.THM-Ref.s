%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJSZvEeck6

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:54 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  298 (1184 expanded)
%              Number of leaves         :   44 ( 378 expanded)
%              Depth                    :   40
%              Number of atoms          : 2585 (24492 expanded)
%              Number of equality atoms :  142 (1652 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('1',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('7',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ X17 @ ( k2_funct_1 @ X17 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('26',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('27',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('29',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_relat_1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('30',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('33',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('41',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('43',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('44',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ~ ( v2_funct_1 @ X17 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X17 ) @ X17 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('46',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('47',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('48',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('55',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('57',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['53','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('66',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['63','66','67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('71',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['48','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['47','77'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('80',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('81',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('82',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('85',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','92'])).

thf('94',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('100',plain,(
    v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['93','94','95','96','97','98','99'])).

thf('101',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('102',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['44','102'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('105',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('106',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('107',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) @ sk_B ),
    inference(demod,[status(thm)],['103','104','105','106','107','108'])).

thf('110',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('111',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) )
    | ( sk_B
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_B
      = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['43','111'])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('114',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('115',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('116',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('118',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['112','113','116','117','118','119','120'])).

thf('122',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('123',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('124',plain,(
    ! [X45: $i] :
      ( ( k6_partfun1 @ X45 )
      = ( k6_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('125',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup+',[status(thm)],['121','126'])).

thf('128',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','127'])).

thf('129',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('130',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('131',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133'])).

thf('135',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','134'])).

thf('136',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('138',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( k6_partfun1 @ sk_B )
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['135','136','137','138','139','140'])).

thf('142',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['40','145'])).

thf('147',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('148',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 )
        = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) ) )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['39','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('152',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('153',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','80','81','82','83'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('155',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['152','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('160',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('161',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('162',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('163',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('165',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('168',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['165','168'])).

thf('170',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('171',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
      = sk_D ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['166','167'])).

thf('173',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('175',plain,(
    ! [X14: $i] :
      ( ( ( k5_relat_1 @ X14 @ ( k6_partfun1 @ ( k2_relat_1 @ X14 ) ) )
        = X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('176',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('178',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('180',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['178','179'])).

thf('181',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('182',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['180','181','182'])).

thf('184',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X6 @ X5 ) ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['183','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ X0 ) ) @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['173','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['166','167'])).

thf('190',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['166','167'])).

thf('191',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('193',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('197',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ( ( k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42 )
        = ( k5_relat_1 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['195','200'])).

thf('202',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['194','203'])).

thf('205',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('207',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('208',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['205','210'])).

thf('212',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('214',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212','213'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('215',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( X27 = X30 )
      | ~ ( r2_relset_1 @ X28 @ X29 @ X27 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('216',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','216'])).

thf('218',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('219',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('221',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('223',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('225',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['223','224'])).

thf('226',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('227',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('229',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('230',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['193','219','220','227','228','229'])).

thf('231',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['217','218'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 )
        = ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('233',plain,
    ( ( ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('235',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ sk_D )
    = sk_D ),
    inference(demod,[status(thm)],['171','172'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['166','167'])).

thf('240',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['233','234','235','236','237','238','239'])).

thf('241',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['51','52'])).

thf('245',plain,
    ( ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','157','158'])).

thf('246',plain,
    ( ( ( k2_funct_1 @ sk_C )
      = sk_D )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151','159','160','230','240','241','242','243','244','245'])).

thf('247',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['64','65'])).

thf('251',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    $false ),
    inference(demod,[status(thm)],['249','250','251'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mJSZvEeck6
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:53:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.35/1.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.35/1.55  % Solved by: fo/fo7.sh
% 1.35/1.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.35/1.55  % done 1691 iterations in 1.108s
% 1.35/1.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.35/1.55  % SZS output start Refutation
% 1.35/1.55  thf(sk_D_type, type, sk_D: $i).
% 1.35/1.55  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.35/1.55  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.35/1.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.35/1.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.35/1.55  thf(sk_B_type, type, sk_B: $i).
% 1.35/1.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.35/1.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.35/1.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.35/1.55  thf(sk_C_type, type, sk_C: $i).
% 1.35/1.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.35/1.55  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.35/1.55  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.35/1.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.35/1.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.35/1.55  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.35/1.55  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.35/1.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.35/1.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.35/1.55  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.35/1.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.35/1.55  thf(sk_A_type, type, sk_A: $i).
% 1.35/1.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.35/1.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.35/1.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.35/1.55  thf(dt_k2_funct_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.55       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 1.35/1.55         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 1.35/1.55  thf('0', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf('1', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf(t61_funct_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.55       ( ( v2_funct_1 @ A ) =>
% 1.35/1.55         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 1.35/1.55             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 1.35/1.55           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 1.35/1.55             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.35/1.55  thf('2', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 1.35/1.55              = (k6_relat_1 @ (k1_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.35/1.55  thf(redefinition_k6_partfun1, axiom,
% 1.35/1.55    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.35/1.55  thf('3', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.35/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.55  thf('4', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 1.35/1.55              = (k6_partfun1 @ (k1_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['2', '3'])).
% 1.35/1.55  thf('5', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf('6', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_relat_1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('cnf', [status(esa)], [t61_funct_1])).
% 1.35/1.55  thf('7', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.35/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.55  thf('8', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf(t55_relat_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ A ) =>
% 1.35/1.55       ( ![B:$i]:
% 1.35/1.55         ( ( v1_relat_1 @ B ) =>
% 1.35/1.55           ( ![C:$i]:
% 1.35/1.55             ( ( v1_relat_1 @ C ) =>
% 1.35/1.55               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 1.35/1.55                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 1.35/1.55  thf('9', plain,
% 1.35/1.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X7)
% 1.35/1.55          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.35/1.55              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 1.35/1.55          | ~ (v1_relat_1 @ X9)
% 1.35/1.55          | ~ (v1_relat_1 @ X8))),
% 1.35/1.55      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.35/1.55  thf('10', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.35/1.55            = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v1_relat_1 @ X0))),
% 1.35/1.55      inference('sup+', [status(thm)], ['8', '9'])).
% 1.35/1.55  thf('11', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.35/1.55              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1))))),
% 1.35/1.55      inference('simplify', [status(thm)], ['10'])).
% 1.35/1.55  thf('12', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.35/1.55              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X1))),
% 1.35/1.55      inference('sup-', [status(thm)], ['5', '11'])).
% 1.35/1.55  thf('13', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.35/1.55              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['12'])).
% 1.35/1.55  thf('14', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 1.35/1.55            = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.35/1.55               (k6_partfun1 @ (k1_relat_1 @ X0))))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['4', '13'])).
% 1.35/1.55  thf('15', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.55              (k2_funct_1 @ X0))
% 1.35/1.55              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.35/1.55                 (k6_partfun1 @ (k1_relat_1 @ X0)))))),
% 1.35/1.55      inference('simplify', [status(thm)], ['14'])).
% 1.35/1.55  thf('16', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.55              (k2_funct_1 @ X0))
% 1.35/1.55              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.35/1.55                 (k6_partfun1 @ (k1_relat_1 @ X0))))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['1', '15'])).
% 1.35/1.55  thf('17', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.55              (k2_funct_1 @ X0))
% 1.35/1.55              = (k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 1.35/1.55                 (k6_partfun1 @ (k1_relat_1 @ X0))))
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['16'])).
% 1.35/1.55  thf('18', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf('19', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ X17 @ (k2_funct_1 @ X17))
% 1.35/1.55              = (k6_partfun1 @ (k1_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['2', '3'])).
% 1.35/1.55  thf('20', plain,
% 1.35/1.55      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X7)
% 1.35/1.55          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.35/1.55              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 1.35/1.55          | ~ (v1_relat_1 @ X9)
% 1.35/1.55          | ~ (v1_relat_1 @ X8))),
% 1.35/1.55      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.35/1.55  thf('21', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 1.35/1.55            = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['19', '20'])).
% 1.35/1.55  thf('22', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 1.35/1.55          | ~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 1.35/1.55              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1))))),
% 1.35/1.55      inference('simplify', [status(thm)], ['21'])).
% 1.35/1.55  thf('23', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 1.35/1.55              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X1))),
% 1.35/1.55      inference('sup-', [status(thm)], ['18', '22'])).
% 1.35/1.55  thf('24', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X1)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X1)
% 1.35/1.55              = (k5_relat_1 @ X0 @ (k5_relat_1 @ (k2_funct_1 @ X0) @ X1)))
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['23'])).
% 1.35/1.55  thf('25', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ 
% 1.35/1.55            (k6_partfun1 @ (k1_relat_1 @ X0)))
% 1.35/1.55            = (k5_relat_1 @ X0 @ 
% 1.35/1.55               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.55                (k2_funct_1 @ X0))))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0))))),
% 1.35/1.55      inference('sup+', [status(thm)], ['17', '24'])).
% 1.35/1.55  thf(t71_relat_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.35/1.55       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.35/1.55  thf('26', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 1.35/1.55      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.35/1.55  thf('27', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.35/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.55  thf('28', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 1.35/1.55      inference('demod', [status(thm)], ['26', '27'])).
% 1.35/1.55  thf(t80_relat_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ A ) =>
% 1.35/1.55       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 1.35/1.55  thf('29', plain,
% 1.35/1.55      (![X14 : $i]:
% 1.35/1.55         (((k5_relat_1 @ X14 @ (k6_relat_1 @ (k2_relat_1 @ X14))) = (X14))
% 1.35/1.55          | ~ (v1_relat_1 @ X14))),
% 1.35/1.55      inference('cnf', [status(esa)], [t80_relat_1])).
% 1.35/1.55  thf('30', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.35/1.55      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.55  thf('31', plain,
% 1.35/1.55      (![X14 : $i]:
% 1.35/1.55         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 1.35/1.55          | ~ (v1_relat_1 @ X14))),
% 1.35/1.55      inference('demod', [status(thm)], ['29', '30'])).
% 1.35/1.55  thf('32', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.35/1.55            = (k6_partfun1 @ X0))
% 1.35/1.55          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['28', '31'])).
% 1.35/1.55  thf(dt_k6_partfun1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( m1_subset_1 @
% 1.35/1.55         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.35/1.55       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.35/1.55  thf('33', plain,
% 1.35/1.55      (![X38 : $i]:
% 1.35/1.55         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 1.35/1.55          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.35/1.55  thf(cc1_relset_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.55       ( v1_relat_1 @ C ) ))).
% 1.35/1.55  thf('34', plain,
% 1.35/1.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.35/1.55         ((v1_relat_1 @ X18)
% 1.35/1.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.35/1.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.35/1.55  thf('35', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.55  thf('36', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.35/1.55           = (k6_partfun1 @ X0))),
% 1.35/1.55      inference('demod', [status(thm)], ['32', '35'])).
% 1.35/1.55  thf('37', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.35/1.55      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.55  thf('38', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.35/1.55            = (k5_relat_1 @ X0 @ 
% 1.35/1.55               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.55                (k2_funct_1 @ X0))))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0))),
% 1.35/1.55      inference('demod', [status(thm)], ['25', '36', '37'])).
% 1.35/1.55  thf('39', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 1.35/1.55              = (k5_relat_1 @ X0 @ 
% 1.35/1.55                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ 
% 1.35/1.55                  (k2_funct_1 @ X0)))))),
% 1.35/1.55      inference('simplify', [status(thm)], ['38'])).
% 1.35/1.55  thf('40', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf('41', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('42', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('43', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('44', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('45', plain,
% 1.35/1.55      (![X17 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X17)
% 1.35/1.55          | ((k5_relat_1 @ (k2_funct_1 @ X17) @ X17)
% 1.35/1.55              = (k6_partfun1 @ (k2_relat_1 @ X17)))
% 1.35/1.55          | ~ (v1_funct_1 @ X17)
% 1.35/1.55          | ~ (v1_relat_1 @ X17))),
% 1.35/1.55      inference('demod', [status(thm)], ['6', '7'])).
% 1.35/1.55  thf('46', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf(t55_funct_1, axiom,
% 1.35/1.55    (![A:$i]:
% 1.35/1.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.35/1.55       ( ( v2_funct_1 @ A ) =>
% 1.35/1.55         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.35/1.55           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.35/1.55  thf('47', plain,
% 1.35/1.55      (![X16 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X16)
% 1.35/1.55          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.35/1.55          | ~ (v1_funct_1 @ X16)
% 1.35/1.55          | ~ (v1_relat_1 @ X16))),
% 1.35/1.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.35/1.55  thf('48', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf(t36_funct_2, conjecture,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.55       ( ![D:$i]:
% 1.35/1.55         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.35/1.55             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.35/1.55           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.35/1.55               ( r2_relset_1 @
% 1.35/1.55                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.35/1.55                 ( k6_partfun1 @ A ) ) & 
% 1.35/1.55               ( v2_funct_1 @ C ) ) =>
% 1.35/1.55             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.55               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 1.35/1.55  thf(zf_stmt_0, negated_conjecture,
% 1.35/1.55    (~( ![A:$i,B:$i,C:$i]:
% 1.35/1.55        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.35/1.55            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.55          ( ![D:$i]:
% 1.35/1.55            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.35/1.55                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.35/1.55              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 1.35/1.55                  ( r2_relset_1 @
% 1.35/1.55                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.35/1.55                    ( k6_partfun1 @ A ) ) & 
% 1.35/1.55                  ( v2_funct_1 @ C ) ) =>
% 1.35/1.55                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.35/1.55                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 1.35/1.55    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 1.35/1.55  thf('49', plain,
% 1.35/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf(redefinition_k2_relset_1, axiom,
% 1.35/1.55    (![A:$i,B:$i,C:$i]:
% 1.35/1.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.35/1.55  thf('50', plain,
% 1.35/1.55      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.35/1.55         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 1.35/1.55          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.35/1.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.35/1.55  thf('51', plain,
% 1.35/1.55      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.35/1.55      inference('sup-', [status(thm)], ['49', '50'])).
% 1.35/1.55  thf('52', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('53', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.55      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.55  thf('54', plain,
% 1.35/1.55      (![X15 : $i]:
% 1.35/1.55         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.55          | ~ (v1_funct_1 @ X15)
% 1.35/1.55          | ~ (v1_relat_1 @ X15))),
% 1.35/1.55      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.55  thf('55', plain,
% 1.35/1.55      (![X16 : $i]:
% 1.35/1.55         (~ (v2_funct_1 @ X16)
% 1.35/1.55          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 1.35/1.55          | ~ (v1_funct_1 @ X16)
% 1.35/1.55          | ~ (v1_relat_1 @ X16))),
% 1.35/1.55      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.35/1.55  thf(d10_xboole_0, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.35/1.55  thf('56', plain,
% 1.35/1.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.35/1.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.55  thf('57', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.55      inference('simplify', [status(thm)], ['56'])).
% 1.35/1.55  thf(d18_relat_1, axiom,
% 1.35/1.55    (![A:$i,B:$i]:
% 1.35/1.55     ( ( v1_relat_1 @ B ) =>
% 1.35/1.55       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.35/1.55  thf('58', plain,
% 1.35/1.55      (![X3 : $i, X4 : $i]:
% 1.35/1.55         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.35/1.55          | (v4_relat_1 @ X3 @ X4)
% 1.35/1.55          | ~ (v1_relat_1 @ X3))),
% 1.35/1.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.35/1.55  thf('59', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['57', '58'])).
% 1.35/1.55  thf('60', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 1.35/1.55      inference('sup+', [status(thm)], ['55', '59'])).
% 1.35/1.55  thf('61', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         (~ (v1_relat_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0)
% 1.35/1.55          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 1.35/1.55      inference('sup-', [status(thm)], ['54', '60'])).
% 1.35/1.55  thf('62', plain,
% 1.35/1.55      (![X0 : $i]:
% 1.35/1.55         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 1.35/1.55          | ~ (v2_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_funct_1 @ X0)
% 1.35/1.55          | ~ (v1_relat_1 @ X0))),
% 1.35/1.55      inference('simplify', [status(thm)], ['61'])).
% 1.35/1.55  thf('63', plain,
% 1.35/1.55      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 1.35/1.55        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.55        | ~ (v2_funct_1 @ sk_C))),
% 1.35/1.55      inference('sup+', [status(thm)], ['53', '62'])).
% 1.35/1.55  thf('64', plain,
% 1.35/1.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('65', plain,
% 1.35/1.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.35/1.55         ((v1_relat_1 @ X18)
% 1.35/1.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.35/1.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.35/1.55  thf('66', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.55      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.55  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('68', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('69', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 1.35/1.55      inference('demod', [status(thm)], ['63', '66', '67', '68'])).
% 1.35/1.55  thf('70', plain,
% 1.35/1.55      (![X3 : $i, X4 : $i]:
% 1.35/1.55         (~ (v4_relat_1 @ X3 @ X4)
% 1.35/1.55          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.35/1.55          | ~ (v1_relat_1 @ X3))),
% 1.35/1.55      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.35/1.55  thf('71', plain,
% 1.35/1.55      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.35/1.55        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.35/1.55      inference('sup-', [status(thm)], ['69', '70'])).
% 1.35/1.55  thf('72', plain,
% 1.35/1.55      ((~ (v1_relat_1 @ sk_C)
% 1.35/1.55        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.55        | (r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B))),
% 1.35/1.55      inference('sup-', [status(thm)], ['48', '71'])).
% 1.35/1.55  thf('73', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.55      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.55  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.55  thf('75', plain, ((r1_tarski @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_B)),
% 1.35/1.55      inference('demod', [status(thm)], ['72', '73', '74'])).
% 1.35/1.55  thf('76', plain,
% 1.35/1.55      (![X0 : $i, X2 : $i]:
% 1.35/1.55         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.56  thf('77', plain,
% 1.35/1.56      ((~ (r1_tarski @ sk_B @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 1.35/1.56        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['75', '76'])).
% 1.35/1.56  thf('78', plain,
% 1.35/1.56      ((~ (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | ((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['47', '77'])).
% 1.35/1.56  thf('79', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('80', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.56      inference('simplify', [status(thm)], ['56'])).
% 1.35/1.56  thf('81', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('82', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('84', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.56      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '83'])).
% 1.35/1.56  thf(t44_relat_1, axiom,
% 1.35/1.56    (![A:$i]:
% 1.35/1.56     ( ( v1_relat_1 @ A ) =>
% 1.35/1.56       ( ![B:$i]:
% 1.35/1.56         ( ( v1_relat_1 @ B ) =>
% 1.35/1.56           ( r1_tarski @
% 1.35/1.56             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 1.35/1.56  thf('85', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X5)
% 1.35/1.56          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.35/1.56             (k1_relat_1 @ X6))
% 1.35/1.56          | ~ (v1_relat_1 @ X6))),
% 1.35/1.56      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.35/1.56  thf('86', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((r1_tarski @ 
% 1.35/1.56           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B)
% 1.35/1.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.35/1.56          | ~ (v1_relat_1 @ X0))),
% 1.35/1.56      inference('sup+', [status(thm)], ['84', '85'])).
% 1.35/1.56  thf('87', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ sk_C)
% 1.35/1.56          | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56          | ~ (v1_relat_1 @ X0)
% 1.35/1.56          | (r1_tarski @ 
% 1.35/1.56             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['46', '86'])).
% 1.35/1.56  thf('88', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('90', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X0)
% 1.35/1.56          | (r1_tarski @ 
% 1.35/1.56             (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)) @ sk_B))),
% 1.35/1.56      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.35/1.56  thf('91', plain,
% 1.35/1.56      (![X3 : $i, X4 : $i]:
% 1.35/1.56         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.35/1.56          | (v4_relat_1 @ X3 @ X4)
% 1.35/1.56          | ~ (v1_relat_1 @ X3))),
% 1.35/1.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.35/1.56  thf('92', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X0)
% 1.35/1.56          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 1.35/1.56          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['90', '91'])).
% 1.35/1.56  thf('93', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C))),
% 1.35/1.56      inference('sup-', [status(thm)], ['45', '92'])).
% 1.35/1.56  thf('94', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('95', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.56  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('99', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('100', plain,
% 1.35/1.56      ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B)),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['93', '94', '95', '96', '97', '98', '99'])).
% 1.35/1.56  thf('101', plain,
% 1.35/1.56      (![X3 : $i, X4 : $i]:
% 1.35/1.56         (~ (v4_relat_1 @ X3 @ X4)
% 1.35/1.56          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.35/1.56          | ~ (v1_relat_1 @ X3))),
% 1.35/1.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.35/1.56  thf('102', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.35/1.56        | (r1_tarski @ 
% 1.35/1.56           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['100', '101'])).
% 1.35/1.56  thf('103', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | (r1_tarski @ 
% 1.35/1.56           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['44', '102'])).
% 1.35/1.56  thf('104', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('105', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.56  thf('106', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('107', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('108', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('109', plain,
% 1.35/1.56      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)) @ 
% 1.35/1.56        sk_B)),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['103', '104', '105', '106', '107', '108'])).
% 1.35/1.56  thf('110', plain,
% 1.35/1.56      (![X0 : $i, X2 : $i]:
% 1.35/1.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.56  thf('111', plain,
% 1.35/1.56      ((~ (r1_tarski @ sk_B @ 
% 1.35/1.56           (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))
% 1.35/1.56        | ((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['109', '110'])).
% 1.35/1.56  thf('112', plain,
% 1.35/1.56      ((~ (r1_tarski @ sk_B @ 
% 1.35/1.56           (k1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C))))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | ((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['43', '111'])).
% 1.35/1.56  thf('113', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('114', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 1.35/1.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.35/1.56  thf('115', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.35/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.56  thf('116', plain,
% 1.35/1.56      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.35/1.56      inference('demod', [status(thm)], ['114', '115'])).
% 1.35/1.56  thf('117', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.56      inference('simplify', [status(thm)], ['56'])).
% 1.35/1.56  thf('118', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('120', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('121', plain,
% 1.35/1.56      (((sk_B) = (k1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['112', '113', '116', '117', '118', '119', '120'])).
% 1.35/1.56  thf('122', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.35/1.56      inference('simplify', [status(thm)], ['56'])).
% 1.35/1.56  thf(t77_relat_1, axiom,
% 1.35/1.56    (![A:$i,B:$i]:
% 1.35/1.56     ( ( v1_relat_1 @ B ) =>
% 1.35/1.56       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 1.35/1.56         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 1.35/1.56  thf('123', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.35/1.56          | ((k5_relat_1 @ (k6_relat_1 @ X13) @ X12) = (X12))
% 1.35/1.56          | ~ (v1_relat_1 @ X12))),
% 1.35/1.56      inference('cnf', [status(esa)], [t77_relat_1])).
% 1.35/1.56  thf('124', plain, (![X45 : $i]: ((k6_partfun1 @ X45) = (k6_relat_1 @ X45))),
% 1.35/1.56      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.35/1.56  thf('125', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 1.35/1.56          | ~ (v1_relat_1 @ X12))),
% 1.35/1.56      inference('demod', [status(thm)], ['123', '124'])).
% 1.35/1.56  thf('126', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X0)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['122', '125'])).
% 1.35/1.56  thf('127', plain,
% 1.35/1.56      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.56          (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.35/1.56          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.35/1.56        | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['121', '126'])).
% 1.35/1.56  thf('128', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.56            (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.35/1.56            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['42', '127'])).
% 1.35/1.56  thf('129', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('130', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.56  thf('131', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('134', plain,
% 1.35/1.56      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.56         (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.35/1.56         = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['128', '129', '130', '131', '132', '133'])).
% 1.35/1.56  thf('135', plain,
% 1.35/1.56      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.56          (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 1.35/1.56          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C))),
% 1.35/1.56      inference('sup+', [status(thm)], ['41', '134'])).
% 1.35/1.56  thf('136', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('137', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 1.35/1.56           = (k6_partfun1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)], ['32', '35'])).
% 1.35/1.56  thf('138', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('140', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('141', plain,
% 1.35/1.56      (((k6_partfun1 @ sk_B) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['135', '136', '137', '138', '139', '140'])).
% 1.35/1.56  thf('142', plain,
% 1.35/1.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X7)
% 1.35/1.56          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.35/1.56              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 1.35/1.56          | ~ (v1_relat_1 @ X9)
% 1.35/1.56          | ~ (v1_relat_1 @ X8))),
% 1.35/1.56      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.35/1.56  thf('143', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.56            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.35/1.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.35/1.56          | ~ (v1_relat_1 @ X0)
% 1.35/1.56          | ~ (v1_relat_1 @ sk_C))),
% 1.35/1.56      inference('sup+', [status(thm)], ['141', '142'])).
% 1.35/1.56  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('145', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.56            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0)))
% 1.35/1.56          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 1.35/1.56          | ~ (v1_relat_1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)], ['143', '144'])).
% 1.35/1.56  thf('146', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ sk_C)
% 1.35/1.56          | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56          | ~ (v1_relat_1 @ X0)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.56              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['40', '145'])).
% 1.35/1.56  thf('147', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('148', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('149', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X0)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)
% 1.35/1.56              = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k5_relat_1 @ sk_C @ X0))))),
% 1.35/1.56      inference('demod', [status(thm)], ['146', '147', '148'])).
% 1.35/1.56  thf('150', plain,
% 1.35/1.56      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ 
% 1.35/1.56          (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 1.35/1.56           (k2_funct_1 @ sk_C)))
% 1.35/1.56          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 1.35/1.56             (k6_partfun1 @ (k1_relat_1 @ sk_C))))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v1_relat_1 @ 
% 1.35/1.56             (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ 
% 1.35/1.56              (k2_funct_1 @ sk_C))))),
% 1.35/1.56      inference('sup+', [status(thm)], ['39', '149'])).
% 1.35/1.56  thf('151', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('152', plain,
% 1.35/1.56      (![X15 : $i]:
% 1.35/1.56         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 1.35/1.56          | ~ (v1_funct_1 @ X15)
% 1.35/1.56          | ~ (v1_relat_1 @ X15))),
% 1.35/1.56      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 1.35/1.56  thf('153', plain, (((sk_B) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.56      inference('demod', [status(thm)], ['78', '79', '80', '81', '82', '83'])).
% 1.35/1.56  thf('154', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X0)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['122', '125'])).
% 1.35/1.56  thf('155', plain,
% 1.35/1.56      ((((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.56          = (k2_funct_1 @ sk_C))
% 1.35/1.56        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['153', '154'])).
% 1.35/1.56  thf('156', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.56            = (k2_funct_1 @ sk_C)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['152', '155'])).
% 1.35/1.56  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('159', plain,
% 1.35/1.56      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.56         = (k2_funct_1 @ sk_C))),
% 1.35/1.56      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.35/1.56  thf('160', plain,
% 1.35/1.56      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.56         = (k2_funct_1 @ sk_C))),
% 1.35/1.56      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.35/1.56  thf('161', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(cc2_relset_1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i]:
% 1.35/1.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.35/1.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.35/1.56  thf('162', plain,
% 1.35/1.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.35/1.56         ((v4_relat_1 @ X21 @ X22)
% 1.35/1.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.35/1.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.35/1.56  thf('163', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 1.35/1.56      inference('sup-', [status(thm)], ['161', '162'])).
% 1.35/1.56  thf('164', plain,
% 1.35/1.56      (![X3 : $i, X4 : $i]:
% 1.35/1.56         (~ (v4_relat_1 @ X3 @ X4)
% 1.35/1.56          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.35/1.56          | ~ (v1_relat_1 @ X3))),
% 1.35/1.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.35/1.56  thf('165', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 1.35/1.56      inference('sup-', [status(thm)], ['163', '164'])).
% 1.35/1.56  thf('166', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('167', plain,
% 1.35/1.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.35/1.56         ((v1_relat_1 @ X18)
% 1.35/1.56          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.35/1.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.35/1.56  thf('168', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.56      inference('sup-', [status(thm)], ['166', '167'])).
% 1.35/1.56  thf('169', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 1.35/1.56      inference('demod', [status(thm)], ['165', '168'])).
% 1.35/1.56  thf('170', plain,
% 1.35/1.56      (![X12 : $i, X13 : $i]:
% 1.35/1.56         (~ (r1_tarski @ (k1_relat_1 @ X12) @ X13)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ X13) @ X12) = (X12))
% 1.35/1.56          | ~ (v1_relat_1 @ X12))),
% 1.35/1.56      inference('demod', [status(thm)], ['123', '124'])).
% 1.35/1.56  thf('171', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ sk_D)
% 1.35/1.56        | ((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['169', '170'])).
% 1.35/1.56  thf('172', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.56      inference('sup-', [status(thm)], ['166', '167'])).
% 1.35/1.56  thf('173', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['171', '172'])).
% 1.35/1.56  thf('174', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('175', plain,
% 1.35/1.56      (![X14 : $i]:
% 1.35/1.56         (((k5_relat_1 @ X14 @ (k6_partfun1 @ (k2_relat_1 @ X14))) = (X14))
% 1.35/1.56          | ~ (v1_relat_1 @ X14))),
% 1.35/1.56      inference('demod', [status(thm)], ['29', '30'])).
% 1.35/1.56  thf('176', plain,
% 1.35/1.56      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C))),
% 1.35/1.56      inference('sup+', [status(thm)], ['174', '175'])).
% 1.35/1.56  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('178', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 1.35/1.56      inference('demod', [status(thm)], ['176', '177'])).
% 1.35/1.56  thf('179', plain,
% 1.35/1.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X7)
% 1.35/1.56          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 1.35/1.56              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 1.35/1.56          | ~ (v1_relat_1 @ X9)
% 1.35/1.56          | ~ (v1_relat_1 @ X8))),
% 1.35/1.56      inference('cnf', [status(esa)], [t55_relat_1])).
% 1.35/1.56  thf('180', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (((k5_relat_1 @ sk_C @ X0)
% 1.35/1.56            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.35/1.56          | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56          | ~ (v1_relat_1 @ X0)
% 1.35/1.56          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['178', '179'])).
% 1.35/1.56  thf('181', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('182', plain, (![X0 : $i]: (v1_relat_1 @ (k6_partfun1 @ X0))),
% 1.35/1.56      inference('sup-', [status(thm)], ['33', '34'])).
% 1.35/1.56  thf('183', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (((k5_relat_1 @ sk_C @ X0)
% 1.35/1.56            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 1.35/1.56          | ~ (v1_relat_1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)], ['180', '181', '182'])).
% 1.35/1.56  thf('184', plain,
% 1.35/1.56      (![X5 : $i, X6 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X5)
% 1.35/1.56          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X6 @ X5)) @ 
% 1.35/1.56             (k1_relat_1 @ X6))
% 1.35/1.56          | ~ (v1_relat_1 @ X6))),
% 1.35/1.56      inference('cnf', [status(esa)], [t44_relat_1])).
% 1.35/1.56  thf('185', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) @ 
% 1.35/1.56           (k1_relat_1 @ sk_C))
% 1.35/1.56          | ~ (v1_relat_1 @ X0)
% 1.35/1.56          | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 1.35/1.56      inference('sup+', [status(thm)], ['183', '184'])).
% 1.35/1.56  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('187', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ X0)) @ 
% 1.35/1.56           (k1_relat_1 @ sk_C))
% 1.35/1.56          | ~ (v1_relat_1 @ X0)
% 1.35/1.56          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))),
% 1.35/1.56      inference('demod', [status(thm)], ['185', '186'])).
% 1.35/1.56  thf('188', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ sk_D)
% 1.35/1.56        | ~ (v1_relat_1 @ sk_D)
% 1.35/1.56        | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 1.35/1.56           (k1_relat_1 @ sk_C)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['173', '187'])).
% 1.35/1.56  thf('189', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.56      inference('sup-', [status(thm)], ['166', '167'])).
% 1.35/1.56  thf('190', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.56      inference('sup-', [status(thm)], ['166', '167'])).
% 1.35/1.56  thf('191', plain,
% 1.35/1.56      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 1.35/1.56        (k1_relat_1 @ sk_C))),
% 1.35/1.56      inference('demod', [status(thm)], ['188', '189', '190'])).
% 1.35/1.56  thf('192', plain,
% 1.35/1.56      (![X0 : $i, X2 : $i]:
% 1.35/1.56         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.35/1.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.35/1.56  thf('193', plain,
% 1.35/1.56      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 1.35/1.56           (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 1.35/1.56        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['191', '192'])).
% 1.35/1.56  thf('194', plain,
% 1.35/1.56      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.35/1.56        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.35/1.56        (k6_partfun1 @ sk_A))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('195', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('196', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(redefinition_k1_partfun1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.35/1.56     ( ( ( v1_funct_1 @ E ) & 
% 1.35/1.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.56         ( v1_funct_1 @ F ) & 
% 1.35/1.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.35/1.56       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 1.35/1.56  thf('197', plain,
% 1.35/1.56      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 1.35/1.56         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 1.35/1.56          | ~ (v1_funct_1 @ X39)
% 1.35/1.56          | ~ (v1_funct_1 @ X42)
% 1.35/1.56          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 1.35/1.56          | ((k1_partfun1 @ X40 @ X41 @ X43 @ X44 @ X39 @ X42)
% 1.35/1.56              = (k5_relat_1 @ X39 @ X42)))),
% 1.35/1.56      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 1.35/1.56  thf('198', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.35/1.56            = (k5_relat_1 @ sk_C @ X0))
% 1.35/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.35/1.56          | ~ (v1_funct_1 @ X0)
% 1.35/1.56          | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.56      inference('sup-', [status(thm)], ['196', '197'])).
% 1.35/1.56  thf('199', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('200', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 1.35/1.56            = (k5_relat_1 @ sk_C @ X0))
% 1.35/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 1.35/1.56          | ~ (v1_funct_1 @ X0))),
% 1.35/1.56      inference('demod', [status(thm)], ['198', '199'])).
% 1.35/1.56  thf('201', plain,
% 1.35/1.56      ((~ (v1_funct_1 @ sk_D)
% 1.35/1.56        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.56            = (k5_relat_1 @ sk_C @ sk_D)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['195', '200'])).
% 1.35/1.56  thf('202', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('203', plain,
% 1.35/1.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.56         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['201', '202'])).
% 1.35/1.56  thf('204', plain,
% 1.35/1.56      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.35/1.56        (k6_partfun1 @ sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['194', '203'])).
% 1.35/1.56  thf('205', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('206', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf(dt_k1_partfun1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.35/1.56     ( ( ( v1_funct_1 @ E ) & 
% 1.35/1.56         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.56         ( v1_funct_1 @ F ) & 
% 1.35/1.56         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.35/1.56       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.35/1.56         ( m1_subset_1 @
% 1.35/1.56           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.35/1.56           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.35/1.56  thf('207', plain,
% 1.35/1.56      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.35/1.56         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.35/1.56          | ~ (v1_funct_1 @ X31)
% 1.35/1.56          | ~ (v1_funct_1 @ X34)
% 1.35/1.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.35/1.56          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 1.35/1.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 1.35/1.56      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.35/1.56  thf('208', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.35/1.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.35/1.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.35/1.56          | ~ (v1_funct_1 @ X1)
% 1.35/1.56          | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.56      inference('sup-', [status(thm)], ['206', '207'])).
% 1.35/1.56  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('210', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.35/1.56         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.35/1.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.35/1.56          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.35/1.56          | ~ (v1_funct_1 @ X1))),
% 1.35/1.56      inference('demod', [status(thm)], ['208', '209'])).
% 1.35/1.56  thf('211', plain,
% 1.35/1.56      ((~ (v1_funct_1 @ sk_D)
% 1.35/1.56        | (m1_subset_1 @ 
% 1.35/1.56           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.35/1.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['205', '210'])).
% 1.35/1.56  thf('212', plain, ((v1_funct_1 @ sk_D)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('213', plain,
% 1.35/1.56      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.35/1.56         = (k5_relat_1 @ sk_C @ sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['201', '202'])).
% 1.35/1.56  thf('214', plain,
% 1.35/1.56      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 1.35/1.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.35/1.56      inference('demod', [status(thm)], ['211', '212', '213'])).
% 1.35/1.56  thf(redefinition_r2_relset_1, axiom,
% 1.35/1.56    (![A:$i,B:$i,C:$i,D:$i]:
% 1.35/1.56     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.35/1.56         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.35/1.56       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.35/1.56  thf('215', plain,
% 1.35/1.56      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.35/1.56         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.35/1.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.35/1.56          | ((X27) = (X30))
% 1.35/1.56          | ~ (r2_relset_1 @ X28 @ X29 @ X27 @ X30))),
% 1.35/1.56      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.35/1.56  thf('216', plain,
% 1.35/1.56      (![X0 : $i]:
% 1.35/1.56         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 1.35/1.56          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 1.35/1.56          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.35/1.56      inference('sup-', [status(thm)], ['214', '215'])).
% 1.35/1.56  thf('217', plain,
% 1.35/1.56      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.35/1.56           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.35/1.56        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 1.35/1.56      inference('sup-', [status(thm)], ['204', '216'])).
% 1.35/1.56  thf('218', plain,
% 1.35/1.56      (![X38 : $i]:
% 1.35/1.56         (m1_subset_1 @ (k6_partfun1 @ X38) @ 
% 1.35/1.56          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X38)))),
% 1.35/1.56      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.35/1.56  thf('219', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['217', '218'])).
% 1.35/1.56  thf('220', plain,
% 1.35/1.56      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.35/1.56      inference('demod', [status(thm)], ['114', '115'])).
% 1.35/1.56  thf('221', plain,
% 1.35/1.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('222', plain,
% 1.35/1.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.35/1.56         ((v4_relat_1 @ X21 @ X22)
% 1.35/1.56          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.35/1.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.35/1.56  thf('223', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 1.35/1.56      inference('sup-', [status(thm)], ['221', '222'])).
% 1.35/1.56  thf('224', plain,
% 1.35/1.56      (![X3 : $i, X4 : $i]:
% 1.35/1.56         (~ (v4_relat_1 @ X3 @ X4)
% 1.35/1.56          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 1.35/1.56          | ~ (v1_relat_1 @ X3))),
% 1.35/1.56      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.35/1.56  thf('225', plain,
% 1.35/1.56      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 1.35/1.56      inference('sup-', [status(thm)], ['223', '224'])).
% 1.35/1.56  thf('226', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('227', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 1.35/1.56      inference('demod', [status(thm)], ['225', '226'])).
% 1.35/1.56  thf('228', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['217', '218'])).
% 1.35/1.56  thf('229', plain,
% 1.35/1.56      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 1.35/1.56      inference('demod', [status(thm)], ['114', '115'])).
% 1.35/1.56  thf('230', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['193', '219', '220', '227', '228', '229'])).
% 1.35/1.56  thf('231', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 1.35/1.56      inference('demod', [status(thm)], ['217', '218'])).
% 1.35/1.56  thf('232', plain,
% 1.35/1.56      (![X0 : $i, X1 : $i]:
% 1.35/1.56         (~ (v1_relat_1 @ X1)
% 1.35/1.56          | ~ (v2_funct_1 @ X0)
% 1.35/1.56          | ((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)
% 1.35/1.56              = (k5_relat_1 @ (k2_funct_1 @ X0) @ (k5_relat_1 @ X0 @ X1)))
% 1.35/1.56          | ~ (v1_funct_1 @ X0)
% 1.35/1.56          | ~ (v1_relat_1 @ X0))),
% 1.35/1.56      inference('simplify', [status(thm)], ['12'])).
% 1.35/1.56  thf('233', plain,
% 1.35/1.56      ((((k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_D)
% 1.35/1.56          = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))
% 1.35/1.56        | ~ (v1_relat_1 @ sk_C)
% 1.35/1.56        | ~ (v1_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v2_funct_1 @ sk_C)
% 1.35/1.56        | ~ (v1_relat_1 @ sk_D))),
% 1.35/1.56      inference('sup+', [status(thm)], ['231', '232'])).
% 1.35/1.56  thf('234', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('235', plain, (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ sk_D) = (sk_D))),
% 1.35/1.56      inference('demod', [status(thm)], ['171', '172'])).
% 1.35/1.56  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('238', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('239', plain, ((v1_relat_1 @ sk_D)),
% 1.35/1.56      inference('sup-', [status(thm)], ['166', '167'])).
% 1.35/1.56  thf('240', plain,
% 1.35/1.56      (((sk_D) = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A)))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['233', '234', '235', '236', '237', '238', '239'])).
% 1.35/1.56  thf('241', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('243', plain, ((v2_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('244', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 1.35/1.56      inference('sup+', [status(thm)], ['51', '52'])).
% 1.35/1.56  thf('245', plain,
% 1.35/1.56      (((k5_relat_1 @ (k6_partfun1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 1.35/1.56         = (k2_funct_1 @ sk_C))),
% 1.35/1.56      inference('demod', [status(thm)], ['156', '157', '158'])).
% 1.35/1.56  thf('246', plain,
% 1.35/1.56      ((((k2_funct_1 @ sk_C) = (sk_D)) | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.35/1.56      inference('demod', [status(thm)],
% 1.35/1.56                ['150', '151', '159', '160', '230', '240', '241', '242', 
% 1.35/1.56                 '243', '244', '245'])).
% 1.35/1.56  thf('247', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('248', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 1.35/1.56      inference('simplify_reflect-', [status(thm)], ['246', '247'])).
% 1.35/1.56  thf('249', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 1.35/1.56      inference('sup-', [status(thm)], ['0', '248'])).
% 1.35/1.56  thf('250', plain, ((v1_relat_1 @ sk_C)),
% 1.35/1.56      inference('sup-', [status(thm)], ['64', '65'])).
% 1.35/1.56  thf('251', plain, ((v1_funct_1 @ sk_C)),
% 1.35/1.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.35/1.56  thf('252', plain, ($false),
% 1.35/1.56      inference('demod', [status(thm)], ['249', '250', '251'])).
% 1.35/1.56  
% 1.35/1.56  % SZS output end Refutation
% 1.35/1.56  
% 1.35/1.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
