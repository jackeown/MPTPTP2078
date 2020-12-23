%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FwILf1Vl9N

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:15 EST 2020

% Result     : Theorem 5.99s
% Output     : Refutation 5.99s
% Verified   : 
% Statistics : Number of formulae       :  407 (5477 expanded)
%              Number of leaves         :   55 (1771 expanded)
%              Depth                    :   31
%              Number of atoms          : 4195 (88602 expanded)
%              Number of equality atoms :  216 (6054 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t53_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ? [B: $i] :
            ( ( ( k5_relat_1 @ A @ B )
              = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
            & ( v1_funct_1 @ B )
            & ( v1_relat_1 @ B ) )
       => ( v2_funct_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X17 @ X16 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X17 ) ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t53_funct_1])).

thf('8',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X17 @ X16 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('19',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('21',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('22',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k1_relat_1 @ X18 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('23',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_relat_1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('24',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('38',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

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

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('40',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('46',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('47',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('51',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) )
        = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['49','54'])).

thf('56',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['37','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('64',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('76',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','77'])).

thf('79',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('80',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_2 @ D @ A @ B )
        & ( v1_funct_1 @ D ) )
     => ! [E: $i] :
          ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
            & ( v1_funct_2 @ E @ B @ C )
            & ( v1_funct_1 @ E ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ D )
                = B )
              & ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) )
           => ( ( ( v2_funct_1 @ E )
                & ( v2_funct_1 @ D ) )
              | ( ( B != k1_xboole_0 )
                & ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i] :
      ( ( zip_tseitin_1 @ C @ B )
     => ( ( C = k1_xboole_0 )
        & ( B != k1_xboole_0 ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [E: $i,D: $i] :
      ( ( zip_tseitin_0 @ E @ D )
     => ( ( v2_funct_1 @ D )
        & ( v2_funct_1 @ E ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
              & ( ( k2_relset_1 @ A @ B @ D )
                = B ) )
           => ( ( zip_tseitin_1 @ C @ B )
              | ( zip_tseitin_0 @ E @ D ) ) ) ) ) )).

thf('82',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( zip_tseitin_0 @ X49 @ X52 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49 ) )
      | ( zip_tseitin_1 @ X51 @ X50 )
      | ( ( k2_relset_1 @ X53 @ X50 @ X52 )
       != X50 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('88',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('89',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('90',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('94',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ( ( k5_relat_1 @ X17 @ X16 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X17 ) ) )
      | ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ ( k1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('100',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('101',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('103',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('104',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('105',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ X0 )
       != ( k6_partfun1 @ X0 ) )
      | ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['98','101','102','103','104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['87','107','108','109','110','111'])).

thf('113',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X47: $i,X48: $i] :
      ( ( X47 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('115',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X45: $i,X46: $i] :
      ( ( v2_funct_1 @ X46 )
      | ~ ( zip_tseitin_0 @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('119',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['59','64','65','119'])).

thf('121',plain,(
    ! [X8: $i] :
      ( ( ( k5_relat_1 @ X8 @ ( k6_partfun1 @ ( k2_relat_1 @ X8 ) ) )
        = X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('122',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('123',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( X26 = X29 )
      | ~ ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 )
      | ( sk_D = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( r2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D ) @ sk_D @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X20 ) )
        = X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('130',plain,(
    m1_subset_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['59','64','65','119'])).

thf('131',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( r2_relset_1 @ X27 @ X28 @ X26 @ X29 )
      | ( X26 != X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('132',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r2_relset_1 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    r2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,
    ( ( r2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D ) @ sk_D @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['129','133'])).

thf('135',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('136',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('138',plain,(
    r2_relset_1 @ sk_B @ ( k2_relat_1 @ sk_D ) @ sk_D @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['134','135','136','137'])).

thf('139',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','138'])).

thf('140',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('141',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('142',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['140','141'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('143',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('146',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('150',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('156',plain,
    ( ( k6_partfun1 @ sk_A )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('158',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('159',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ X19 @ ( k2_funct_1 @ X19 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('161',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ X58 @ ( k2_funct_1 @ X58 ) )
        = ( k6_partfun1 @ X59 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('162',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['162','163','164','165','166'])).

thf('168',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
      = ( k6_partfun1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['159','170'])).

thf('172',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('176',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( k6_partfun1 @ ( k1_relat_1 @ sk_C ) )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['171','176','177','178'])).

thf('180',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('181',plain,
    ( ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('183',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['181','182'])).

thf(t66_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( v2_funct_1 @ B ) )
           => ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('184',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf(t82_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ! [D: $i] :
              ( ( v1_relat_1 @ D )
             => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
                  & ( ( k5_relat_1 @ B @ C )
                    = ( k6_relat_1 @ ( k1_relat_1 @ D ) ) )
                  & ( ( k5_relat_1 @ C @ D )
                    = ( k6_relat_1 @ A ) ) )
               => ( D = B ) ) ) ) ) )).

thf('185',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k5_relat_1 @ X9 @ X12 )
       != ( k6_relat_1 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t82_relat_1])).

thf('186',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('187',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('188',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ X9 )
       != ( k6_partfun1 @ ( k1_relat_1 @ X12 ) ) )
      | ( ( k5_relat_1 @ X9 @ X12 )
       != ( k6_partfun1 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( X2
        = ( k2_funct_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ X2 )
       != ( k6_partfun1 @ X3 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X3 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['184','188'])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ sk_C )
       != ( k6_partfun1 @ X2 ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['183','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('192',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
       != ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ X2 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ sk_C )
       != ( k6_partfun1 @ X2 ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k6_partfun1 @ sk_A ) )
       != ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
      | ( sk_C
        = ( k2_funct_1 @ sk_D ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['156','192'])).

thf('194',plain,(
    ! [X19: $i] :
      ( ~ ( v2_funct_1 @ X19 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X19 ) @ X19 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X19 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('195',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X6 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) @ ( k6_partfun1 @ X0 ) )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('199',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('200',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) @ ( k6_partfun1 @ X0 ) )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k2_relat_1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['194','201'])).

thf('203',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X7 ) )
      = X7 ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('204',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('205',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('206',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('208',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['174','175'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('212',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('216',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('219',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('220',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['214','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('225',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['224','229'])).

thf('231',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('232',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ ( k6_partfun1 @ X0 ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('234',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ X1 @ ( k6_partfun1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('236',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ sk_D )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['234','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['241','242'])).

thf('244',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('245',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('247',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['238','243','244','245','246'])).

thf('248',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['223','247'])).

thf('249',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','138'])).

thf('250',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('251',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('253',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['248','249','250','251','252'])).

thf('254',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('255',plain,(
    ! [X57: $i,X58: $i,X59: $i] :
      ( ( X57 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X58 )
      | ~ ( v1_funct_2 @ X58 @ X59 @ X57 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X57 ) ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X58 ) @ X58 )
        = ( k6_partfun1 @ X57 ) )
      | ~ ( v2_funct_1 @ X58 )
      | ( ( k2_relset_1 @ X59 @ X57 @ X58 )
       != X57 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('256',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('259',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['256','257','258','259','260'])).

thf('262',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_partfun1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['261'])).

thf('263',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['262','263'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('266',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['128','138'])).

thf('267',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('268',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['266','267'])).

thf('269',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('270',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('272',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('273',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['271','272'])).

thf('274',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('275',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_partfun1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['273','274'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['270','275'])).

thf('277',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['276','277'])).

thf('279',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('280',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('281',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('282',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('284',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['279','284'])).

thf('286',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('288',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['278','287'])).

thf('289',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('290',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('292',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['290','291'])).

thf('293',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k2_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['202','203','204','205','206'])).

thf('294',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_funct_1 @ ( k5_relat_1 @ X22 @ X21 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X21 ) @ ( k2_funct_1 @ X22 ) ) )
      | ~ ( v2_funct_1 @ X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t66_funct_1])).

thf('295',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X14: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X14 ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('297',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('298',plain,(
    ! [X0: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['295','296','297','298'])).

thf('300',plain,(
    ! [X13: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('301',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ X1 ) @ ( k6_partfun1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['299','300'])).

thf('302',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v2_funct_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_relat_1 @ sk_D )
      | ( v1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['292','301'])).

thf('303',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('304',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('305',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('306',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['304','305'])).

thf('307',plain,(
    ! [X15: $i] :
      ( v1_funct_1 @ ( k6_partfun1 @ X15 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('308',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['306','307'])).

thf('309',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ sk_D )
      | ( v1_funct_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['303','308'])).

thf('310',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('311',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['309','310'])).

thf('312',plain,(
    ! [X0: $i] :
      ( ( k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ ( k6_partfun1 @ X0 ) @ sk_D )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['285','286'])).

thf('313',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['311','312'])).

thf('314',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('315',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('316',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('317',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k6_partfun1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['302','313','314','315','316'])).

thf('318',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['269','317'])).

thf('319',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('320',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('321',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('322',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['318','319','320','321'])).

thf('323',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['268','322'])).

thf('324',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['248','249','250','251','252'])).

thf('325',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['323','324'])).

thf('326',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['265','325'])).

thf('327',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['62','63'])).

thf('328',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['117','118'])).

thf('330',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['326','327','328','329'])).

thf('331',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('332',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( v2_funct_1 @ X54 )
      | ( ( k2_relset_1 @ X56 @ X55 @ X54 )
       != X55 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X56 ) ) )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X55 ) ) )
      | ~ ( v1_funct_2 @ X54 @ X56 @ X55 )
      | ~ ( v1_funct_1 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('333',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('338',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['333','334','335','336','337'])).

thf('339',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['338'])).

thf('340',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('341',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('343',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['341','342'])).

thf('344',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ sk_A )
       != ( k6_partfun1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ sk_D ) )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ X0 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['193','207','208','209','210','211','212','213','253','264','330','343'])).

thf('345',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ( ( k6_partfun1 @ sk_B )
       != ( k6_partfun1 @ X0 ) )
      | ( sk_C
        = ( k2_funct_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['344'])).

thf('346',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_D ) )
    | ( ( k6_partfun1 @ sk_B )
     != ( k6_partfun1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['146','345'])).

thf('347',plain,
    ( sk_C
    = ( k2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['346'])).

thf('348',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['139','347'])).

thf('349',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['348','349'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FwILf1Vl9N
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.99/6.25  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.99/6.25  % Solved by: fo/fo7.sh
% 5.99/6.25  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.99/6.25  % done 4674 iterations in 5.796s
% 5.99/6.25  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.99/6.25  % SZS output start Refutation
% 5.99/6.25  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.99/6.25  thf(sk_A_type, type, sk_A: $i).
% 5.99/6.25  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 5.99/6.25  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.99/6.25  thf(sk_D_type, type, sk_D: $i).
% 5.99/6.25  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.99/6.25  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.99/6.25  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 5.99/6.25  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 5.99/6.25  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 5.99/6.25  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 5.99/6.25  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.99/6.25  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 5.99/6.25  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 5.99/6.25  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 5.99/6.25  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 5.99/6.25  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 5.99/6.25  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.99/6.25  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 5.99/6.25  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 5.99/6.25  thf(sk_B_type, type, sk_B: $i).
% 5.99/6.25  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.99/6.25  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 5.99/6.25  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.99/6.25  thf(sk_C_type, type, sk_C: $i).
% 5.99/6.25  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 5.99/6.25  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 5.99/6.25  thf(t55_funct_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.99/6.25       ( ( v2_funct_1 @ A ) =>
% 5.99/6.25         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 5.99/6.25           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 5.99/6.25  thf('0', plain,
% 5.99/6.25      (![X18 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X18)
% 5.99/6.25          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 5.99/6.25          | ~ (v1_funct_1 @ X18)
% 5.99/6.25          | ~ (v1_relat_1 @ X18))),
% 5.99/6.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.99/6.25  thf(dt_k2_funct_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.99/6.25       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 5.99/6.25         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 5.99/6.25  thf('1', plain,
% 5.99/6.25      (![X13 : $i]:
% 5.99/6.25         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.99/6.25          | ~ (v1_funct_1 @ X13)
% 5.99/6.25          | ~ (v1_relat_1 @ X13))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.25  thf('2', plain,
% 5.99/6.25      (![X13 : $i]:
% 5.99/6.25         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.99/6.25          | ~ (v1_funct_1 @ X13)
% 5.99/6.25          | ~ (v1_relat_1 @ X13))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.25  thf('3', plain,
% 5.99/6.25      (![X18 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X18)
% 5.99/6.25          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 5.99/6.25          | ~ (v1_funct_1 @ X18)
% 5.99/6.25          | ~ (v1_relat_1 @ X18))),
% 5.99/6.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.99/6.25  thf(t61_funct_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.99/6.25       ( ( v2_funct_1 @ A ) =>
% 5.99/6.25         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 5.99/6.25             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 5.99/6.25           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 5.99/6.25             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 5.99/6.25  thf('4', plain,
% 5.99/6.25      (![X19 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X19)
% 5.99/6.25          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 5.99/6.25              = (k6_relat_1 @ (k2_relat_1 @ X19)))
% 5.99/6.25          | ~ (v1_funct_1 @ X19)
% 5.99/6.25          | ~ (v1_relat_1 @ X19))),
% 5.99/6.25      inference('cnf', [status(esa)], [t61_funct_1])).
% 5.99/6.25  thf(redefinition_k6_partfun1, axiom,
% 5.99/6.25    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 5.99/6.25  thf('5', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.25      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.25  thf('6', plain,
% 5.99/6.25      (![X19 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X19)
% 5.99/6.25          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 5.99/6.25              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 5.99/6.25          | ~ (v1_funct_1 @ X19)
% 5.99/6.25          | ~ (v1_relat_1 @ X19))),
% 5.99/6.25      inference('demod', [status(thm)], ['4', '5'])).
% 5.99/6.25  thf(t53_funct_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.99/6.25       ( ( ?[B:$i]:
% 5.99/6.25           ( ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 5.99/6.25             ( v1_funct_1 @ B ) & ( v1_relat_1 @ B ) ) ) =>
% 5.99/6.25         ( v2_funct_1 @ A ) ) ))).
% 5.99/6.25  thf('7', plain,
% 5.99/6.25      (![X16 : $i, X17 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X16)
% 5.99/6.25          | ~ (v1_funct_1 @ X16)
% 5.99/6.25          | ((k5_relat_1 @ X17 @ X16) != (k6_relat_1 @ (k1_relat_1 @ X17)))
% 5.99/6.25          | (v2_funct_1 @ X17)
% 5.99/6.25          | ~ (v1_funct_1 @ X17)
% 5.99/6.25          | ~ (v1_relat_1 @ X17))),
% 5.99/6.25      inference('cnf', [status(esa)], [t53_funct_1])).
% 5.99/6.25  thf('8', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.25      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.25  thf('9', plain,
% 5.99/6.25      (![X16 : $i, X17 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X16)
% 5.99/6.25          | ~ (v1_funct_1 @ X16)
% 5.99/6.25          | ((k5_relat_1 @ X17 @ X16) != (k6_partfun1 @ (k1_relat_1 @ X17)))
% 5.99/6.25          | (v2_funct_1 @ X17)
% 5.99/6.25          | ~ (v1_funct_1 @ X17)
% 5.99/6.25          | ~ (v1_relat_1 @ X17))),
% 5.99/6.25      inference('demod', [status(thm)], ['7', '8'])).
% 5.99/6.25  thf('10', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 5.99/6.25            != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('sup-', [status(thm)], ['6', '9'])).
% 5.99/6.25  thf('11', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ((k6_partfun1 @ (k2_relat_1 @ X0))
% 5.99/6.25              != (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 5.99/6.25      inference('simplify', [status(thm)], ['10'])).
% 5.99/6.25  thf('12', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k6_partfun1 @ (k2_relat_1 @ X0))
% 5.99/6.25            != (k6_partfun1 @ (k2_relat_1 @ X0)))
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.99/6.25      inference('sup-', [status(thm)], ['3', '11'])).
% 5.99/6.25  thf('13', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['12'])).
% 5.99/6.25  thf('14', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.99/6.25      inference('sup-', [status(thm)], ['2', '13'])).
% 5.99/6.25  thf('15', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['14'])).
% 5.99/6.25  thf('16', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.99/6.25      inference('sup-', [status(thm)], ['1', '15'])).
% 5.99/6.25  thf('17', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['16'])).
% 5.99/6.25  thf('18', plain,
% 5.99/6.25      (![X13 : $i]:
% 5.99/6.25         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.99/6.25          | ~ (v1_funct_1 @ X13)
% 5.99/6.25          | ~ (v1_relat_1 @ X13))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.25  thf('19', plain,
% 5.99/6.25      (![X13 : $i]:
% 5.99/6.25         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.99/6.25          | ~ (v1_funct_1 @ X13)
% 5.99/6.25          | ~ (v1_relat_1 @ X13))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.25  thf(t65_funct_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.99/6.25       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 5.99/6.25  thf('20', plain,
% 5.99/6.25      (![X20 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X20)
% 5.99/6.25          | ((k2_funct_1 @ (k2_funct_1 @ X20)) = (X20))
% 5.99/6.25          | ~ (v1_funct_1 @ X20)
% 5.99/6.25          | ~ (v1_relat_1 @ X20))),
% 5.99/6.25      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.99/6.25  thf('21', plain,
% 5.99/6.25      (![X13 : $i]:
% 5.99/6.25         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.99/6.25          | ~ (v1_funct_1 @ X13)
% 5.99/6.25          | ~ (v1_relat_1 @ X13))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.25  thf('22', plain,
% 5.99/6.25      (![X18 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X18)
% 5.99/6.25          | ((k1_relat_1 @ X18) = (k2_relat_1 @ (k2_funct_1 @ X18)))
% 5.99/6.25          | ~ (v1_funct_1 @ X18)
% 5.99/6.25          | ~ (v1_relat_1 @ X18))),
% 5.99/6.25      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.99/6.25  thf(t80_relat_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( v1_relat_1 @ A ) =>
% 5.99/6.25       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 5.99/6.25  thf('23', plain,
% 5.99/6.25      (![X8 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X8 @ (k6_relat_1 @ (k2_relat_1 @ X8))) = (X8))
% 5.99/6.25          | ~ (v1_relat_1 @ X8))),
% 5.99/6.25      inference('cnf', [status(esa)], [t80_relat_1])).
% 5.99/6.25  thf('24', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.25      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.25  thf('25', plain,
% 5.99/6.25      (![X8 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 5.99/6.25          | ~ (v1_relat_1 @ X8))),
% 5.99/6.25      inference('demod', [status(thm)], ['23', '24'])).
% 5.99/6.25  thf('26', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.99/6.25            = (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 5.99/6.25      inference('sup+', [status(thm)], ['22', '25'])).
% 5.99/6.25  thf('27', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 5.99/6.25              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 5.99/6.25      inference('sup-', [status(thm)], ['21', '26'])).
% 5.99/6.25  thf('28', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.99/6.25            = (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['27'])).
% 5.99/6.25  thf('29', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 5.99/6.25      inference('sup+', [status(thm)], ['20', '28'])).
% 5.99/6.25  thf('30', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ((k5_relat_1 @ X0 @ 
% 5.99/6.25              (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['19', '29'])).
% 5.99/6.25  thf('31', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['30'])).
% 5.99/6.25  thf('32', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ((k5_relat_1 @ X0 @ 
% 5.99/6.25              (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['18', '31'])).
% 5.99/6.25  thf('33', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['32'])).
% 5.99/6.25  thf('34', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ((k5_relat_1 @ X0 @ 
% 5.99/6.25              (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['17', '33'])).
% 5.99/6.25  thf('35', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.25            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0))),
% 5.99/6.25      inference('simplify', [status(thm)], ['34'])).
% 5.99/6.25  thf('36', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 5.99/6.25            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v2_funct_1 @ X0))),
% 5.99/6.25      inference('sup+', [status(thm)], ['0', '35'])).
% 5.99/6.25  thf('37', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v2_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X0)
% 5.99/6.25          | ((k5_relat_1 @ X0 @ (k6_partfun1 @ (k2_relat_1 @ X0)))
% 5.99/6.25              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 5.99/6.25      inference('simplify', [status(thm)], ['36'])).
% 5.99/6.25  thf(dt_k6_partfun1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( m1_subset_1 @
% 5.99/6.25         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 5.99/6.25       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 5.99/6.25  thf('38', plain,
% 5.99/6.25      (![X37 : $i]:
% 5.99/6.25         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.25          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.25  thf(t36_funct_2, conjecture,
% 5.99/6.25    (![A:$i,B:$i,C:$i]:
% 5.99/6.25     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.25         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.25       ( ![D:$i]:
% 5.99/6.25         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.99/6.25             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.99/6.25           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.99/6.25               ( r2_relset_1 @
% 5.99/6.25                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.99/6.25                 ( k6_partfun1 @ A ) ) & 
% 5.99/6.25               ( v2_funct_1 @ C ) ) =>
% 5.99/6.25             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.99/6.25               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 5.99/6.25  thf(zf_stmt_0, negated_conjecture,
% 5.99/6.25    (~( ![A:$i,B:$i,C:$i]:
% 5.99/6.25        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.25            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.25          ( ![D:$i]:
% 5.99/6.25            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 5.99/6.25                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 5.99/6.25              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 5.99/6.25                  ( r2_relset_1 @
% 5.99/6.25                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 5.99/6.25                    ( k6_partfun1 @ A ) ) & 
% 5.99/6.25                  ( v2_funct_1 @ C ) ) =>
% 5.99/6.25                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.99/6.25                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 5.99/6.25    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 5.99/6.25  thf('39', plain,
% 5.99/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf(dt_k1_partfun1, axiom,
% 5.99/6.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.99/6.25     ( ( ( v1_funct_1 @ E ) & 
% 5.99/6.25         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.99/6.25         ( v1_funct_1 @ F ) & 
% 5.99/6.25         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.99/6.25       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 5.99/6.25         ( m1_subset_1 @
% 5.99/6.25           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 5.99/6.25           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 5.99/6.25  thf('40', plain,
% 5.99/6.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.99/6.25         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 5.99/6.25          | ~ (v1_funct_1 @ X30)
% 5.99/6.25          | ~ (v1_funct_1 @ X33)
% 5.99/6.25          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.99/6.25          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 5.99/6.25             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.99/6.25  thf('41', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.25         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 5.99/6.25           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 5.99/6.25          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.99/6.25          | ~ (v1_funct_1 @ X1)
% 5.99/6.25          | ~ (v1_funct_1 @ sk_D))),
% 5.99/6.25      inference('sup-', [status(thm)], ['39', '40'])).
% 5.99/6.25  thf('42', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('43', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.25         ((m1_subset_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X0 @ sk_D @ X1) @ 
% 5.99/6.25           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 5.99/6.25          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.99/6.25          | ~ (v1_funct_1 @ X1))),
% 5.99/6.25      inference('demod', [status(thm)], ['41', '42'])).
% 5.99/6.25  thf('44', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.25          | (m1_subset_1 @ 
% 5.99/6.25             (k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0)) @ 
% 5.99/6.25             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['38', '43'])).
% 5.99/6.25  thf(fc3_funct_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 5.99/6.25       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 5.99/6.25  thf('45', plain, (![X15 : $i]: (v1_funct_1 @ (k6_relat_1 @ X15))),
% 5.99/6.25      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.99/6.25  thf('46', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.25      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.25  thf('47', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.25      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.25  thf('48', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (m1_subset_1 @ 
% 5.99/6.25          (k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0)) @ 
% 5.99/6.25          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))),
% 5.99/6.25      inference('demod', [status(thm)], ['44', '47'])).
% 5.99/6.25  thf('49', plain,
% 5.99/6.25      (![X37 : $i]:
% 5.99/6.25         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.25          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.25  thf('50', plain,
% 5.99/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf(redefinition_k1_partfun1, axiom,
% 5.99/6.25    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 5.99/6.25     ( ( ( v1_funct_1 @ E ) & 
% 5.99/6.25         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.99/6.25         ( v1_funct_1 @ F ) & 
% 5.99/6.25         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 5.99/6.25       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 5.99/6.25  thf('51', plain,
% 5.99/6.25      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.99/6.25         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.99/6.25          | ~ (v1_funct_1 @ X38)
% 5.99/6.25          | ~ (v1_funct_1 @ X41)
% 5.99/6.25          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.99/6.25          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 5.99/6.25              = (k5_relat_1 @ X38 @ X41)))),
% 5.99/6.25      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.99/6.25  thf('52', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.25         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 5.99/6.25            = (k5_relat_1 @ sk_D @ X0))
% 5.99/6.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.99/6.25          | ~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_1 @ sk_D))),
% 5.99/6.25      inference('sup-', [status(thm)], ['50', '51'])).
% 5.99/6.25  thf('53', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('54', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.25         (((k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0)
% 5.99/6.25            = (k5_relat_1 @ sk_D @ X0))
% 5.99/6.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.99/6.25          | ~ (v1_funct_1 @ X0))),
% 5.99/6.25      inference('demod', [status(thm)], ['52', '53'])).
% 5.99/6.25  thf('55', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.25          | ((k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0))
% 5.99/6.25              = (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['49', '54'])).
% 5.99/6.25  thf('56', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.25      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.25  thf('57', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         ((k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0))
% 5.99/6.25           = (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)))),
% 5.99/6.25      inference('demod', [status(thm)], ['55', '56'])).
% 5.99/6.25  thf('58', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (m1_subset_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)) @ 
% 5.99/6.25          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))),
% 5.99/6.25      inference('demod', [status(thm)], ['48', '57'])).
% 5.99/6.25  thf('59', plain,
% 5.99/6.25      (((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ 
% 5.99/6.25         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D))))
% 5.99/6.25        | ~ (v1_relat_1 @ sk_D)
% 5.99/6.25        | ~ (v1_funct_1 @ sk_D)
% 5.99/6.25        | ~ (v2_funct_1 @ sk_D))),
% 5.99/6.25      inference('sup+', [status(thm)], ['37', '58'])).
% 5.99/6.25  thf('60', plain,
% 5.99/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf(cc2_relat_1, axiom,
% 5.99/6.25    (![A:$i]:
% 5.99/6.25     ( ( v1_relat_1 @ A ) =>
% 5.99/6.25       ( ![B:$i]:
% 5.99/6.25         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 5.99/6.25  thf('61', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i]:
% 5.99/6.25         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.99/6.25          | (v1_relat_1 @ X0)
% 5.99/6.25          | ~ (v1_relat_1 @ X1))),
% 5.99/6.25      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.99/6.25  thf('62', plain,
% 5.99/6.25      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 5.99/6.25      inference('sup-', [status(thm)], ['60', '61'])).
% 5.99/6.25  thf(fc6_relat_1, axiom,
% 5.99/6.25    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 5.99/6.25  thf('63', plain,
% 5.99/6.25      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.99/6.25      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.99/6.25  thf('64', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.25      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.25  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('66', plain,
% 5.99/6.25      ((r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.25        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.99/6.25        (k6_partfun1 @ sk_A))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('67', plain,
% 5.99/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('68', plain,
% 5.99/6.25      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('69', plain,
% 5.99/6.25      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.99/6.25         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 5.99/6.25          | ~ (v1_funct_1 @ X30)
% 5.99/6.25          | ~ (v1_funct_1 @ X33)
% 5.99/6.25          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.99/6.25          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 5.99/6.25             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.99/6.25  thf('70', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.25         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.99/6.25           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.99/6.25          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.99/6.25          | ~ (v1_funct_1 @ X1)
% 5.99/6.25          | ~ (v1_funct_1 @ sk_C))),
% 5.99/6.25      inference('sup-', [status(thm)], ['68', '69'])).
% 5.99/6.25  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('72', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.25         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 5.99/6.25           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 5.99/6.25          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 5.99/6.25          | ~ (v1_funct_1 @ X1))),
% 5.99/6.25      inference('demod', [status(thm)], ['70', '71'])).
% 5.99/6.25  thf('73', plain,
% 5.99/6.25      ((~ (v1_funct_1 @ sk_D)
% 5.99/6.25        | (m1_subset_1 @ 
% 5.99/6.25           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.99/6.25           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['67', '72'])).
% 5.99/6.25  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf('75', plain,
% 5.99/6.25      ((m1_subset_1 @ 
% 5.99/6.25        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 5.99/6.25        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 5.99/6.25      inference('demod', [status(thm)], ['73', '74'])).
% 5.99/6.25  thf(redefinition_r2_relset_1, axiom,
% 5.99/6.25    (![A:$i,B:$i,C:$i,D:$i]:
% 5.99/6.25     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.99/6.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.25       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 5.99/6.25  thf('76', plain,
% 5.99/6.25      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.99/6.25         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.25          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.25          | ((X26) = (X29))
% 5.99/6.25          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 5.99/6.25      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.99/6.25  thf('77', plain,
% 5.99/6.25      (![X0 : $i]:
% 5.99/6.25         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 5.99/6.25             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 5.99/6.25          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 5.99/6.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 5.99/6.25      inference('sup-', [status(thm)], ['75', '76'])).
% 5.99/6.25  thf('78', plain,
% 5.99/6.25      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 5.99/6.25           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 5.99/6.25        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.99/6.25            = (k6_partfun1 @ sk_A)))),
% 5.99/6.25      inference('sup-', [status(thm)], ['66', '77'])).
% 5.99/6.25  thf('79', plain,
% 5.99/6.25      (![X37 : $i]:
% 5.99/6.25         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.25          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.25      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.25  thf('80', plain,
% 5.99/6.25      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.99/6.25         = (k6_partfun1 @ sk_A))),
% 5.99/6.25      inference('demod', [status(thm)], ['78', '79'])).
% 5.99/6.25  thf('81', plain,
% 5.99/6.25      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.25  thf(t30_funct_2, axiom,
% 5.99/6.25    (![A:$i,B:$i,C:$i,D:$i]:
% 5.99/6.25     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 5.99/6.25         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 5.99/6.25       ( ![E:$i]:
% 5.99/6.25         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 5.99/6.25             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 5.99/6.25           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 5.99/6.25               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 5.99/6.25             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 5.99/6.25               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 5.99/6.25  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 5.99/6.25  thf(zf_stmt_2, axiom,
% 5.99/6.25    (![C:$i,B:$i]:
% 5.99/6.25     ( ( zip_tseitin_1 @ C @ B ) =>
% 5.99/6.25       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 5.99/6.25  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 5.99/6.25  thf(zf_stmt_4, axiom,
% 5.99/6.25    (![E:$i,D:$i]:
% 5.99/6.25     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 5.99/6.25  thf(zf_stmt_5, axiom,
% 5.99/6.25    (![A:$i,B:$i,C:$i,D:$i]:
% 5.99/6.25     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 5.99/6.25         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.25       ( ![E:$i]:
% 5.99/6.25         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 5.99/6.25             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 5.99/6.25           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 5.99/6.25               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 5.99/6.25             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 5.99/6.25  thf('82', plain,
% 5.99/6.25      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i]:
% 5.99/6.25         (~ (v1_funct_1 @ X49)
% 5.99/6.25          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 5.99/6.25          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 5.99/6.25          | (zip_tseitin_0 @ X49 @ X52)
% 5.99/6.25          | ~ (v2_funct_1 @ (k1_partfun1 @ X53 @ X50 @ X50 @ X51 @ X52 @ X49))
% 5.99/6.25          | (zip_tseitin_1 @ X51 @ X50)
% 5.99/6.25          | ((k2_relset_1 @ X53 @ X50 @ X52) != (X50))
% 5.99/6.25          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X50)))
% 5.99/6.25          | ~ (v1_funct_2 @ X52 @ X53 @ X50)
% 5.99/6.25          | ~ (v1_funct_1 @ X52))),
% 5.99/6.25      inference('cnf', [status(esa)], [zf_stmt_5])).
% 5.99/6.25  thf('83', plain,
% 5.99/6.25      (![X0 : $i, X1 : $i]:
% 5.99/6.25         (~ (v1_funct_1 @ X0)
% 5.99/6.25          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.99/6.25          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.99/6.26          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 5.99/6.26          | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.99/6.26          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 5.99/6.26          | (zip_tseitin_0 @ sk_D @ X0)
% 5.99/6.26          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_D))),
% 5.99/6.26      inference('sup-', [status(thm)], ['81', '82'])).
% 5.99/6.26  thf('84', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('85', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('86', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 5.99/6.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 5.99/6.26          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 5.99/6.26          | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.99/6.26          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 5.99/6.26          | (zip_tseitin_0 @ sk_D @ X0))),
% 5.99/6.26      inference('demod', [status(thm)], ['83', '84', '85'])).
% 5.99/6.26  thf('87', plain,
% 5.99/6.26      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 5.99/6.26        | (zip_tseitin_0 @ sk_D @ sk_C)
% 5.99/6.26        | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.99/6.26        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.99/6.26        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 5.99/6.26        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_C))),
% 5.99/6.26      inference('sup-', [status(thm)], ['80', '86'])).
% 5.99/6.26  thf(t71_relat_1, axiom,
% 5.99/6.26    (![A:$i]:
% 5.99/6.26     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 5.99/6.26       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 5.99/6.26  thf('88', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 5.99/6.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.99/6.26  thf('89', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.26  thf('90', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 5.99/6.26      inference('demod', [status(thm)], ['88', '89'])).
% 5.99/6.26  thf('91', plain,
% 5.99/6.26      (![X8 : $i]:
% 5.99/6.26         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 5.99/6.26          | ~ (v1_relat_1 @ X8))),
% 5.99/6.26      inference('demod', [status(thm)], ['23', '24'])).
% 5.99/6.26  thf('92', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 5.99/6.26            = (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup+', [status(thm)], ['90', '91'])).
% 5.99/6.26  thf('93', plain, (![X14 : $i]: (v1_relat_1 @ (k6_relat_1 @ X14))),
% 5.99/6.26      inference('cnf', [status(esa)], [fc3_funct_1])).
% 5.99/6.26  thf('94', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.26  thf('95', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('96', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 5.99/6.26           = (k6_partfun1 @ X0))),
% 5.99/6.26      inference('demod', [status(thm)], ['92', '95'])).
% 5.99/6.26  thf('97', plain,
% 5.99/6.26      (![X16 : $i, X17 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ X16)
% 5.99/6.26          | ~ (v1_funct_1 @ X16)
% 5.99/6.26          | ((k5_relat_1 @ X17 @ X16) != (k6_partfun1 @ (k1_relat_1 @ X17)))
% 5.99/6.26          | (v2_funct_1 @ X17)
% 5.99/6.26          | ~ (v1_funct_1 @ X17)
% 5.99/6.26          | ~ (v1_relat_1 @ X17))),
% 5.99/6.26      inference('demod', [status(thm)], ['7', '8'])).
% 5.99/6.26  thf('98', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k6_partfun1 @ X0)
% 5.99/6.26            != (k6_partfun1 @ (k1_relat_1 @ (k6_partfun1 @ X0))))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | (v2_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['96', '97'])).
% 5.99/6.26  thf('99', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X6)) = (X6))),
% 5.99/6.26      inference('cnf', [status(esa)], [t71_relat_1])).
% 5.99/6.26  thf('100', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.26  thf('101', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 5.99/6.26      inference('demod', [status(thm)], ['99', '100'])).
% 5.99/6.26  thf('102', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('103', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('104', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('105', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('106', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k6_partfun1 @ X0) != (k6_partfun1 @ X0))
% 5.99/6.26          | (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)],
% 5.99/6.26                ['98', '101', '102', '103', '104', '105'])).
% 5.99/6.26  thf('107', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['106'])).
% 5.99/6.26  thf('108', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('109', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('110', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('111', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('112', plain,
% 5.99/6.26      (((zip_tseitin_0 @ sk_D @ sk_C)
% 5.99/6.26        | (zip_tseitin_1 @ sk_A @ sk_B)
% 5.99/6.26        | ((sk_B) != (sk_B)))),
% 5.99/6.26      inference('demod', [status(thm)],
% 5.99/6.26                ['87', '107', '108', '109', '110', '111'])).
% 5.99/6.26  thf('113', plain,
% 5.99/6.26      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 5.99/6.26      inference('simplify', [status(thm)], ['112'])).
% 5.99/6.26  thf('114', plain,
% 5.99/6.26      (![X47 : $i, X48 : $i]:
% 5.99/6.26         (((X47) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X47 @ X48))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.99/6.26  thf('115', plain,
% 5.99/6.26      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['113', '114'])).
% 5.99/6.26  thf('116', plain, (((sk_A) != (k1_xboole_0))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('117', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 5.99/6.26      inference('simplify_reflect-', [status(thm)], ['115', '116'])).
% 5.99/6.26  thf('118', plain,
% 5.99/6.26      (![X45 : $i, X46 : $i]:
% 5.99/6.26         ((v2_funct_1 @ X46) | ~ (zip_tseitin_0 @ X46 @ X45))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_4])).
% 5.99/6.26  thf('119', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('120', plain,
% 5.99/6.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ 
% 5.99/6.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D))))),
% 5.99/6.26      inference('demod', [status(thm)], ['59', '64', '65', '119'])).
% 5.99/6.26  thf('121', plain,
% 5.99/6.26      (![X8 : $i]:
% 5.99/6.26         (((k5_relat_1 @ X8 @ (k6_partfun1 @ (k2_relat_1 @ X8))) = (X8))
% 5.99/6.26          | ~ (v1_relat_1 @ X8))),
% 5.99/6.26      inference('demod', [status(thm)], ['23', '24'])).
% 5.99/6.26  thf('122', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['48', '57'])).
% 5.99/6.26  thf('123', plain,
% 5.99/6.26      (((m1_subset_1 @ sk_D @ 
% 5.99/6.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D))))
% 5.99/6.26        | ~ (v1_relat_1 @ sk_D))),
% 5.99/6.26      inference('sup+', [status(thm)], ['121', '122'])).
% 5.99/6.26  thf('124', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('125', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ 
% 5.99/6.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D))))),
% 5.99/6.26      inference('demod', [status(thm)], ['123', '124'])).
% 5.99/6.26  thf('126', plain,
% 5.99/6.26      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.26          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.26          | ((X26) = (X29))
% 5.99/6.26          | ~ (r2_relset_1 @ X27 @ X28 @ X26 @ X29))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.99/6.26  thf('127', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (r2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D) @ sk_D @ X0)
% 5.99/6.26          | ((sk_D) = (X0))
% 5.99/6.26          | ~ (m1_subset_1 @ X0 @ 
% 5.99/6.26               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D)))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['125', '126'])).
% 5.99/6.26  thf('128', plain,
% 5.99/6.26      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 5.99/6.26        | ~ (r2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D) @ sk_D @ 
% 5.99/6.26             (k2_funct_1 @ (k2_funct_1 @ sk_D))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['120', '127'])).
% 5.99/6.26  thf('129', plain,
% 5.99/6.26      (![X20 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X20)
% 5.99/6.26          | ((k2_funct_1 @ (k2_funct_1 @ X20)) = (X20))
% 5.99/6.26          | ~ (v1_funct_1 @ X20)
% 5.99/6.26          | ~ (v1_relat_1 @ X20))),
% 5.99/6.26      inference('cnf', [status(esa)], [t65_funct_1])).
% 5.99/6.26  thf('130', plain,
% 5.99/6.26      ((m1_subset_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ 
% 5.99/6.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D))))),
% 5.99/6.26      inference('demod', [status(thm)], ['59', '64', '65', '119'])).
% 5.99/6.26  thf('131', plain,
% 5.99/6.26      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.26          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 5.99/6.26          | (r2_relset_1 @ X27 @ X28 @ X26 @ X29)
% 5.99/6.26          | ((X26) != (X29)))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 5.99/6.26  thf('132', plain,
% 5.99/6.26      (![X27 : $i, X28 : $i, X29 : $i]:
% 5.99/6.26         ((r2_relset_1 @ X27 @ X28 @ X29 @ X29)
% 5.99/6.26          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 5.99/6.26      inference('simplify', [status(thm)], ['131'])).
% 5.99/6.26  thf('133', plain,
% 5.99/6.26      ((r2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D) @ 
% 5.99/6.26        (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['130', '132'])).
% 5.99/6.26  thf('134', plain,
% 5.99/6.26      (((r2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D) @ sk_D @ 
% 5.99/6.26         (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 5.99/6.26        | ~ (v1_relat_1 @ sk_D)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26        | ~ (v2_funct_1 @ sk_D))),
% 5.99/6.26      inference('sup+', [status(thm)], ['129', '133'])).
% 5.99/6.26  thf('135', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('136', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('137', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('138', plain,
% 5.99/6.26      ((r2_relset_1 @ sk_B @ (k2_relat_1 @ sk_D) @ sk_D @ 
% 5.99/6.26        (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['134', '135', '136', '137'])).
% 5.99/6.26  thf('139', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['128', '138'])).
% 5.99/6.26  thf('140', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf(cc2_relset_1, axiom,
% 5.99/6.26    (![A:$i,B:$i,C:$i]:
% 5.99/6.26     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 5.99/6.26       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 5.99/6.26  thf('141', plain,
% 5.99/6.26      (![X23 : $i, X24 : $i, X25 : $i]:
% 5.99/6.26         ((v4_relat_1 @ X23 @ X24)
% 5.99/6.26          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 5.99/6.26      inference('cnf', [status(esa)], [cc2_relset_1])).
% 5.99/6.26  thf('142', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 5.99/6.26      inference('sup-', [status(thm)], ['140', '141'])).
% 5.99/6.26  thf(d18_relat_1, axiom,
% 5.99/6.26    (![A:$i,B:$i]:
% 5.99/6.26     ( ( v1_relat_1 @ B ) =>
% 5.99/6.26       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 5.99/6.26  thf('143', plain,
% 5.99/6.26      (![X2 : $i, X3 : $i]:
% 5.99/6.26         (~ (v4_relat_1 @ X2 @ X3)
% 5.99/6.26          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 5.99/6.26          | ~ (v1_relat_1 @ X2))),
% 5.99/6.26      inference('cnf', [status(esa)], [d18_relat_1])).
% 5.99/6.26  thf('144', plain,
% 5.99/6.26      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B))),
% 5.99/6.26      inference('sup-', [status(thm)], ['142', '143'])).
% 5.99/6.26  thf('145', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('146', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 5.99/6.26      inference('demod', [status(thm)], ['144', '145'])).
% 5.99/6.26  thf('147', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('148', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('149', plain,
% 5.99/6.26      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.99/6.26          | ~ (v1_funct_1 @ X38)
% 5.99/6.26          | ~ (v1_funct_1 @ X41)
% 5.99/6.26          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.99/6.26          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 5.99/6.26              = (k5_relat_1 @ X38 @ X41)))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.99/6.26  thf('150', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.26         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.99/6.26            = (k5_relat_1 @ sk_C @ X0))
% 5.99/6.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_C))),
% 5.99/6.26      inference('sup-', [status(thm)], ['148', '149'])).
% 5.99/6.26  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('152', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.26         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 5.99/6.26            = (k5_relat_1 @ sk_C @ X0))
% 5.99/6.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ X0))),
% 5.99/6.26      inference('demod', [status(thm)], ['150', '151'])).
% 5.99/6.26  thf('153', plain,
% 5.99/6.26      ((~ (v1_funct_1 @ sk_D)
% 5.99/6.26        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.99/6.26            = (k5_relat_1 @ sk_C @ sk_D)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['147', '152'])).
% 5.99/6.26  thf('154', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('155', plain,
% 5.99/6.26      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 5.99/6.26         = (k6_partfun1 @ sk_A))),
% 5.99/6.26      inference('demod', [status(thm)], ['78', '79'])).
% 5.99/6.26  thf('156', plain, (((k6_partfun1 @ sk_A) = (k5_relat_1 @ sk_C @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['153', '154', '155'])).
% 5.99/6.26  thf('157', plain,
% 5.99/6.26      (![X19 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X19)
% 5.99/6.26          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 5.99/6.26              = (k6_relat_1 @ (k1_relat_1 @ X19)))
% 5.99/6.26          | ~ (v1_funct_1 @ X19)
% 5.99/6.26          | ~ (v1_relat_1 @ X19))),
% 5.99/6.26      inference('cnf', [status(esa)], [t61_funct_1])).
% 5.99/6.26  thf('158', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.26  thf('159', plain,
% 5.99/6.26      (![X19 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X19)
% 5.99/6.26          | ((k5_relat_1 @ X19 @ (k2_funct_1 @ X19))
% 5.99/6.26              = (k6_partfun1 @ (k1_relat_1 @ X19)))
% 5.99/6.26          | ~ (v1_funct_1 @ X19)
% 5.99/6.26          | ~ (v1_relat_1 @ X19))),
% 5.99/6.26      inference('demod', [status(thm)], ['157', '158'])).
% 5.99/6.26  thf('160', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf(t35_funct_2, axiom,
% 5.99/6.26    (![A:$i,B:$i,C:$i]:
% 5.99/6.26     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.26       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 5.99/6.26         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 5.99/6.26           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 5.99/6.26             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 5.99/6.26  thf('161', plain,
% 5.99/6.26      (![X57 : $i, X58 : $i, X59 : $i]:
% 5.99/6.26         (((X57) = (k1_xboole_0))
% 5.99/6.26          | ~ (v1_funct_1 @ X58)
% 5.99/6.26          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 5.99/6.26          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 5.99/6.26          | ((k5_relat_1 @ X58 @ (k2_funct_1 @ X58)) = (k6_partfun1 @ X59))
% 5.99/6.26          | ~ (v2_funct_1 @ X58)
% 5.99/6.26          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 5.99/6.26      inference('cnf', [status(esa)], [t35_funct_2])).
% 5.99/6.26  thf('162', plain,
% 5.99/6.26      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.99/6.26        | ~ (v2_funct_1 @ sk_C)
% 5.99/6.26        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 5.99/6.26        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_C)
% 5.99/6.26        | ((sk_B) = (k1_xboole_0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['160', '161'])).
% 5.99/6.26  thf('163', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('165', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('167', plain,
% 5.99/6.26      ((((sk_B) != (sk_B))
% 5.99/6.26        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 5.99/6.26        | ((sk_B) = (k1_xboole_0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['162', '163', '164', '165', '166'])).
% 5.99/6.26  thf('168', plain,
% 5.99/6.26      ((((sk_B) = (k1_xboole_0))
% 5.99/6.26        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A)))),
% 5.99/6.26      inference('simplify', [status(thm)], ['167'])).
% 5.99/6.26  thf('169', plain, (((sk_B) != (k1_xboole_0))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('170', plain,
% 5.99/6.26      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 5.99/6.26      inference('simplify_reflect-', [status(thm)], ['168', '169'])).
% 5.99/6.26  thf('171', plain,
% 5.99/6.26      ((((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))
% 5.99/6.26        | ~ (v1_relat_1 @ sk_C)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_C)
% 5.99/6.26        | ~ (v2_funct_1 @ sk_C))),
% 5.99/6.26      inference('sup+', [status(thm)], ['159', '170'])).
% 5.99/6.26  thf('172', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('173', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.99/6.26          | (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.99/6.26  thf('174', plain,
% 5.99/6.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 5.99/6.26      inference('sup-', [status(thm)], ['172', '173'])).
% 5.99/6.26  thf('175', plain,
% 5.99/6.26      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.99/6.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.99/6.26  thf('176', plain, ((v1_relat_1 @ sk_C)),
% 5.99/6.26      inference('demod', [status(thm)], ['174', '175'])).
% 5.99/6.26  thf('177', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('178', plain, ((v2_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('179', plain,
% 5.99/6.26      (((k6_partfun1 @ (k1_relat_1 @ sk_C)) = (k6_partfun1 @ sk_A))),
% 5.99/6.26      inference('demod', [status(thm)], ['171', '176', '177', '178'])).
% 5.99/6.26  thf('180', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 5.99/6.26      inference('demod', [status(thm)], ['99', '100'])).
% 5.99/6.26  thf('181', plain,
% 5.99/6.26      (((k1_relat_1 @ (k6_partfun1 @ sk_A)) = (k1_relat_1 @ sk_C))),
% 5.99/6.26      inference('sup+', [status(thm)], ['179', '180'])).
% 5.99/6.26  thf('182', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 5.99/6.26      inference('demod', [status(thm)], ['99', '100'])).
% 5.99/6.26  thf('183', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 5.99/6.26      inference('demod', [status(thm)], ['181', '182'])).
% 5.99/6.26  thf(t66_funct_1, axiom,
% 5.99/6.26    (![A:$i]:
% 5.99/6.26     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.99/6.26       ( ![B:$i]:
% 5.99/6.26         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.99/6.26           ( ( ( v2_funct_1 @ A ) & ( v2_funct_1 @ B ) ) =>
% 5.99/6.26             ( ( k2_funct_1 @ ( k5_relat_1 @ A @ B ) ) =
% 5.99/6.26               ( k5_relat_1 @ ( k2_funct_1 @ B ) @ ( k2_funct_1 @ A ) ) ) ) ) ) ))).
% 5.99/6.26  thf('184', plain,
% 5.99/6.26      (![X21 : $i, X22 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ X21)
% 5.99/6.26          | ~ (v1_funct_1 @ X21)
% 5.99/6.26          | ((k2_funct_1 @ (k5_relat_1 @ X22 @ X21))
% 5.99/6.26              = (k5_relat_1 @ (k2_funct_1 @ X21) @ (k2_funct_1 @ X22)))
% 5.99/6.26          | ~ (v2_funct_1 @ X21)
% 5.99/6.26          | ~ (v2_funct_1 @ X22)
% 5.99/6.26          | ~ (v1_funct_1 @ X22)
% 5.99/6.26          | ~ (v1_relat_1 @ X22))),
% 5.99/6.26      inference('cnf', [status(esa)], [t66_funct_1])).
% 5.99/6.26  thf(t82_relat_1, axiom,
% 5.99/6.26    (![A:$i,B:$i]:
% 5.99/6.26     ( ( v1_relat_1 @ B ) =>
% 5.99/6.26       ( ![C:$i]:
% 5.99/6.26         ( ( v1_relat_1 @ C ) =>
% 5.99/6.26           ( ![D:$i]:
% 5.99/6.26             ( ( v1_relat_1 @ D ) =>
% 5.99/6.26               ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) & 
% 5.99/6.26                   ( ( k5_relat_1 @ B @ C ) =
% 5.99/6.26                     ( k6_relat_1 @ ( k1_relat_1 @ D ) ) ) & 
% 5.99/6.26                   ( ( k5_relat_1 @ C @ D ) = ( k6_relat_1 @ A ) ) ) =>
% 5.99/6.26                 ( ( D ) = ( B ) ) ) ) ) ) ) ))).
% 5.99/6.26  thf('185', plain,
% 5.99/6.26      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ X9)
% 5.99/6.26          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 5.99/6.26          | ((k5_relat_1 @ X10 @ X9) != (k6_relat_1 @ (k1_relat_1 @ X12)))
% 5.99/6.26          | ((k5_relat_1 @ X9 @ X12) != (k6_relat_1 @ X11))
% 5.99/6.26          | ((X12) = (X10))
% 5.99/6.26          | ~ (v1_relat_1 @ X12)
% 5.99/6.26          | ~ (v1_relat_1 @ X10))),
% 5.99/6.26      inference('cnf', [status(esa)], [t82_relat_1])).
% 5.99/6.26  thf('186', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.26  thf('187', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 5.99/6.26  thf('188', plain,
% 5.99/6.26      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ X9)
% 5.99/6.26          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 5.99/6.26          | ((k5_relat_1 @ X10 @ X9) != (k6_partfun1 @ (k1_relat_1 @ X12)))
% 5.99/6.26          | ((k5_relat_1 @ X9 @ X12) != (k6_partfun1 @ X11))
% 5.99/6.26          | ((X12) = (X10))
% 5.99/6.26          | ~ (v1_relat_1 @ X12)
% 5.99/6.26          | ~ (v1_relat_1 @ X10))),
% 5.99/6.26      inference('demod', [status(thm)], ['185', '186', '187'])).
% 5.99/6.26  thf('189', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 5.99/6.26            != (k6_partfun1 @ (k1_relat_1 @ X2)))
% 5.99/6.26          | ~ (v1_relat_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ X2)
% 5.99/6.26          | ((X2) = (k2_funct_1 @ X0))
% 5.99/6.26          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ X2) != (k6_partfun1 @ X3))
% 5.99/6.26          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ X3)
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['184', '188'])).
% 5.99/6.26  thf('190', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0)) != (k6_partfun1 @ sk_A))
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 5.99/6.26          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ X2)
% 5.99/6.26          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ sk_C) != (k6_partfun1 @ X2))
% 5.99/6.26          | ((sk_C) = (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ sk_C)
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('sup-', [status(thm)], ['183', '189'])).
% 5.99/6.26  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 5.99/6.26      inference('demod', [status(thm)], ['174', '175'])).
% 5.99/6.26  thf('192', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ X1 @ X0)) != (k6_partfun1 @ sk_A))
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ X1))
% 5.99/6.26          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ X2)
% 5.99/6.26          | ((k5_relat_1 @ (k2_funct_1 @ X1) @ sk_C) != (k6_partfun1 @ X2))
% 5.99/6.26          | ((sk_C) = (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('demod', [status(thm)], ['190', '191'])).
% 5.99/6.26  thf('193', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k6_partfun1 @ sk_A)) != (k6_partfun1 @ sk_A))
% 5.99/6.26          | ~ (v1_relat_1 @ sk_C)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_C)
% 5.99/6.26          | ~ (v2_funct_1 @ sk_C)
% 5.99/6.26          | ~ (v2_funct_1 @ sk_D)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26          | ~ (v1_relat_1 @ sk_D)
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 5.99/6.26          | ((sk_C) = (k2_funct_1 @ sk_D))
% 5.99/6.26          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) != (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_D)) @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['156', '192'])).
% 5.99/6.26  thf('194', plain,
% 5.99/6.26      (![X19 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X19)
% 5.99/6.26          | ((k5_relat_1 @ (k2_funct_1 @ X19) @ X19)
% 5.99/6.26              = (k6_partfun1 @ (k2_relat_1 @ X19)))
% 5.99/6.26          | ~ (v1_funct_1 @ X19)
% 5.99/6.26          | ~ (v1_relat_1 @ X19))),
% 5.99/6.26      inference('demod', [status(thm)], ['4', '5'])).
% 5.99/6.26  thf('195', plain, (![X6 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X6)) = (X6))),
% 5.99/6.26      inference('demod', [status(thm)], ['99', '100'])).
% 5.99/6.26  thf('196', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.99/6.26            = (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['27'])).
% 5.99/6.26  thf('197', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k5_relat_1 @ (k2_funct_1 @ (k6_partfun1 @ X0)) @ (k6_partfun1 @ X0))
% 5.99/6.26            = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup+', [status(thm)], ['195', '196'])).
% 5.99/6.26  thf('198', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('199', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('200', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['106'])).
% 5.99/6.26  thf('201', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         ((k5_relat_1 @ (k2_funct_1 @ (k6_partfun1 @ X0)) @ (k6_partfun1 @ X0))
% 5.99/6.26           = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 5.99/6.26  thf('202', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k6_partfun1 @ (k2_relat_1 @ (k6_partfun1 @ X0)))
% 5.99/6.26            = (k2_funct_1 @ (k6_partfun1 @ X0)))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup+', [status(thm)], ['194', '201'])).
% 5.99/6.26  thf('203', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X7)) = (X7))),
% 5.99/6.26      inference('demod', [status(thm)], ['88', '89'])).
% 5.99/6.26  thf('204', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('205', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('206', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['106'])).
% 5.99/6.26  thf('207', plain,
% 5.99/6.26      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 5.99/6.26  thf('208', plain, ((v1_relat_1 @ sk_C)),
% 5.99/6.26      inference('demod', [status(thm)], ['174', '175'])).
% 5.99/6.26  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('210', plain, ((v2_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('211', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('212', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('213', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('214', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k5_relat_1 @ X0 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 5.99/6.26            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['34'])).
% 5.99/6.26  thf('215', plain,
% 5.99/6.26      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 5.99/6.26  thf('216', plain,
% 5.99/6.26      (![X21 : $i, X22 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ X21)
% 5.99/6.26          | ~ (v1_funct_1 @ X21)
% 5.99/6.26          | ((k2_funct_1 @ (k5_relat_1 @ X22 @ X21))
% 5.99/6.26              = (k5_relat_1 @ (k2_funct_1 @ X21) @ (k2_funct_1 @ X22)))
% 5.99/6.26          | ~ (v2_funct_1 @ X21)
% 5.99/6.26          | ~ (v2_funct_1 @ X22)
% 5.99/6.26          | ~ (v1_funct_1 @ X22)
% 5.99/6.26          | ~ (v1_relat_1 @ X22))),
% 5.99/6.26      inference('cnf', [status(esa)], [t66_funct_1])).
% 5.99/6.26  thf('217', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 5.99/6.26            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 5.99/6.26          | ~ (v1_relat_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup+', [status(thm)], ['215', '216'])).
% 5.99/6.26  thf('218', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['106'])).
% 5.99/6.26  thf('219', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('220', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('221', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 5.99/6.26            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 5.99/6.26          | ~ (v1_relat_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ X1))),
% 5.99/6.26      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 5.99/6.26  thf('222', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.26            = (k5_relat_1 @ (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 5.99/6.26               (k2_funct_1 @ X0)))
% 5.99/6.26          | ~ (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0))),
% 5.99/6.26      inference('sup+', [status(thm)], ['214', '221'])).
% 5.99/6.26  thf('223', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0)
% 5.99/6.26          | ((k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 5.99/6.26              = (k5_relat_1 @ 
% 5.99/6.26                 (k6_partfun1 @ (k1_relat_1 @ (k2_funct_1 @ X0))) @ 
% 5.99/6.26                 (k2_funct_1 @ X0))))),
% 5.99/6.26      inference('simplify', [status(thm)], ['222'])).
% 5.99/6.26  thf('224', plain,
% 5.99/6.26      (![X37 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.26  thf('225', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('226', plain,
% 5.99/6.26      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 5.99/6.26          | ~ (v1_funct_1 @ X30)
% 5.99/6.26          | ~ (v1_funct_1 @ X33)
% 5.99/6.26          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.99/6.26          | (v1_funct_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.99/6.26  thf('227', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.26         ((v1_funct_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0))
% 5.99/6.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_D))),
% 5.99/6.26      inference('sup-', [status(thm)], ['225', '226'])).
% 5.99/6.26  thf('228', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('229', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.99/6.26         ((v1_funct_1 @ (k1_partfun1 @ sk_B @ sk_A @ X2 @ X1 @ sk_D @ X0))
% 5.99/6.26          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ X0))),
% 5.99/6.26      inference('demod', [status(thm)], ['227', '228'])).
% 5.99/6.26  thf('230', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | (v1_funct_1 @ 
% 5.99/6.26             (k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['224', '229'])).
% 5.99/6.26  thf('231', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('232', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (v1_funct_1 @ 
% 5.99/6.26          (k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['230', '231'])).
% 5.99/6.26  thf('233', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         ((k1_partfun1 @ sk_B @ sk_A @ X0 @ X0 @ sk_D @ (k6_partfun1 @ X0))
% 5.99/6.26           = (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['55', '56'])).
% 5.99/6.26  thf('234', plain,
% 5.99/6.26      (![X0 : $i]: (v1_funct_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['232', '233'])).
% 5.99/6.26  thf('235', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ X1 @ (k6_partfun1 @ X0)))
% 5.99/6.26            = (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ X1)))
% 5.99/6.26          | ~ (v1_relat_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ X1))),
% 5.99/6.26      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 5.99/6.26  thf('236', plain,
% 5.99/6.26      (![X13 : $i]:
% 5.99/6.26         ((v1_relat_1 @ (k2_funct_1 @ X13))
% 5.99/6.26          | ~ (v1_funct_1 @ X13)
% 5.99/6.26          | ~ (v1_relat_1 @ X13))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.26  thf('237', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X1) @ (k2_funct_1 @ X0)))
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ (k5_relat_1 @ X0 @ (k6_partfun1 @ X1))))),
% 5.99/6.26      inference('sup+', [status(thm)], ['235', '236'])).
% 5.99/6.26  thf('238', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)))
% 5.99/6.26          | ~ (v1_relat_1 @ sk_D)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26          | ~ (v2_funct_1 @ sk_D)
% 5.99/6.26          | (v1_relat_1 @ 
% 5.99/6.26             (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ sk_D))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['234', '237'])).
% 5.99/6.26  thf('239', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['48', '57'])).
% 5.99/6.26  thf('240', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.99/6.26          | (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.99/6.26  thf('241', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ X0))
% 5.99/6.26          | (v1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['239', '240'])).
% 5.99/6.26  thf('242', plain,
% 5.99/6.26      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.99/6.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.99/6.26  thf('243', plain,
% 5.99/6.26      (![X0 : $i]: (v1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['241', '242'])).
% 5.99/6.26  thf('244', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('245', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('246', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('247', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['238', '243', '244', '245', '246'])).
% 5.99/6.26  thf('248', plain,
% 5.99/6.26      (((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D))))
% 5.99/6.26        | ~ (v1_relat_1 @ sk_D)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26        | ~ (v2_funct_1 @ sk_D))),
% 5.99/6.26      inference('sup+', [status(thm)], ['223', '247'])).
% 5.99/6.26  thf('249', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['128', '138'])).
% 5.99/6.26  thf('250', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('251', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('252', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('253', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['248', '249', '250', '251', '252'])).
% 5.99/6.26  thf('254', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('255', plain,
% 5.99/6.26      (![X57 : $i, X58 : $i, X59 : $i]:
% 5.99/6.26         (((X57) = (k1_xboole_0))
% 5.99/6.26          | ~ (v1_funct_1 @ X58)
% 5.99/6.26          | ~ (v1_funct_2 @ X58 @ X59 @ X57)
% 5.99/6.26          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X57)))
% 5.99/6.26          | ((k5_relat_1 @ (k2_funct_1 @ X58) @ X58) = (k6_partfun1 @ X57))
% 5.99/6.26          | ~ (v2_funct_1 @ X58)
% 5.99/6.26          | ((k2_relset_1 @ X59 @ X57 @ X58) != (X57)))),
% 5.99/6.26      inference('cnf', [status(esa)], [t35_funct_2])).
% 5.99/6.26  thf('256', plain,
% 5.99/6.26      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.99/6.26        | ~ (v2_funct_1 @ sk_C)
% 5.99/6.26        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 5.99/6.26        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_C)
% 5.99/6.26        | ((sk_B) = (k1_xboole_0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['254', '255'])).
% 5.99/6.26  thf('257', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('258', plain, ((v2_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('259', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('260', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('261', plain,
% 5.99/6.26      ((((sk_B) != (sk_B))
% 5.99/6.26        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))
% 5.99/6.26        | ((sk_B) = (k1_xboole_0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['256', '257', '258', '259', '260'])).
% 5.99/6.26  thf('262', plain,
% 5.99/6.26      ((((sk_B) = (k1_xboole_0))
% 5.99/6.26        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B)))),
% 5.99/6.26      inference('simplify', [status(thm)], ['261'])).
% 5.99/6.26  thf('263', plain, (((sk_B) != (k1_xboole_0))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('264', plain,
% 5.99/6.26      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 5.99/6.26      inference('simplify_reflect-', [status(thm)], ['262', '263'])).
% 5.99/6.26  thf('265', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['16'])).
% 5.99/6.26  thf('266', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['128', '138'])).
% 5.99/6.26  thf('267', plain,
% 5.99/6.26      (![X18 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X18)
% 5.99/6.26          | ((k2_relat_1 @ X18) = (k1_relat_1 @ (k2_funct_1 @ X18)))
% 5.99/6.26          | ~ (v1_funct_1 @ X18)
% 5.99/6.26          | ~ (v1_relat_1 @ X18))),
% 5.99/6.26      inference('cnf', [status(esa)], [t55_funct_1])).
% 5.99/6.26  thf('268', plain,
% 5.99/6.26      ((((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (k1_relat_1 @ sk_D))
% 5.99/6.26        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 5.99/6.26        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 5.99/6.26        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('sup+', [status(thm)], ['266', '267'])).
% 5.99/6.26  thf('269', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 5.99/6.26            = (k2_funct_1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_funct_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['27'])).
% 5.99/6.26  thf('270', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('271', plain,
% 5.99/6.26      (![X37 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.26  thf('272', plain,
% 5.99/6.26      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 5.99/6.26          | ~ (v1_funct_1 @ X30)
% 5.99/6.26          | ~ (v1_funct_1 @ X33)
% 5.99/6.26          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.99/6.26          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 5.99/6.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.99/6.26  thf('273', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         ((m1_subset_1 @ 
% 5.99/6.26           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_partfun1 @ X0) @ X2) @ 
% 5.99/6.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 5.99/6.26          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ X2)
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['271', '272'])).
% 5.99/6.26  thf('274', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('275', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         ((m1_subset_1 @ 
% 5.99/6.26           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_partfun1 @ X0) @ X2) @ 
% 5.99/6.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 5.99/6.26          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 5.99/6.26          | ~ (v1_funct_1 @ X2))),
% 5.99/6.26      inference('demod', [status(thm)], ['273', '274'])).
% 5.99/6.26  thf('276', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_funct_1 @ sk_D)
% 5.99/6.26          | (m1_subset_1 @ 
% 5.99/6.26             (k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D) @ 
% 5.99/6.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['270', '275'])).
% 5.99/6.26  thf('277', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('278', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (m1_subset_1 @ 
% 5.99/6.26          (k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 5.99/6.26      inference('demod', [status(thm)], ['276', '277'])).
% 5.99/6.26  thf('279', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('280', plain,
% 5.99/6.26      (![X37 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.26  thf('281', plain,
% 5.99/6.26      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 5.99/6.26          | ~ (v1_funct_1 @ X38)
% 5.99/6.26          | ~ (v1_funct_1 @ X41)
% 5.99/6.26          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 5.99/6.26          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 5.99/6.26              = (k5_relat_1 @ X38 @ X41)))),
% 5.99/6.26      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 5.99/6.26  thf('282', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_partfun1 @ X0) @ X1)
% 5.99/6.26            = (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['280', '281'])).
% 5.99/6.26  thf('283', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('284', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_partfun1 @ X0) @ X1)
% 5.99/6.26            = (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 5.99/6.26          | ~ (v1_funct_1 @ X1))),
% 5.99/6.26      inference('demod', [status(thm)], ['282', '283'])).
% 5.99/6.26  thf('285', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_funct_1 @ sk_D)
% 5.99/6.26          | ((k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D)
% 5.99/6.26              = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['279', '284'])).
% 5.99/6.26  thf('286', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('287', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         ((k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D)
% 5.99/6.26           = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['285', '286'])).
% 5.99/6.26  thf('288', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A)))),
% 5.99/6.26      inference('demod', [status(thm)], ['278', '287'])).
% 5.99/6.26  thf('289', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.99/6.26          | (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.99/6.26  thf('290', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ sk_A))
% 5.99/6.26          | (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['288', '289'])).
% 5.99/6.26  thf('291', plain,
% 5.99/6.26      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.99/6.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.99/6.26  thf('292', plain,
% 5.99/6.26      (![X0 : $i]: (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['290', '291'])).
% 5.99/6.26  thf('293', plain,
% 5.99/6.26      (![X0 : $i]: ((k6_partfun1 @ X0) = (k2_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['202', '203', '204', '205', '206'])).
% 5.99/6.26  thf('294', plain,
% 5.99/6.26      (![X21 : $i, X22 : $i]:
% 5.99/6.26         (~ (v1_relat_1 @ X21)
% 5.99/6.26          | ~ (v1_funct_1 @ X21)
% 5.99/6.26          | ((k2_funct_1 @ (k5_relat_1 @ X22 @ X21))
% 5.99/6.26              = (k5_relat_1 @ (k2_funct_1 @ X21) @ (k2_funct_1 @ X22)))
% 5.99/6.26          | ~ (v2_funct_1 @ X21)
% 5.99/6.26          | ~ (v2_funct_1 @ X22)
% 5.99/6.26          | ~ (v1_funct_1 @ X22)
% 5.99/6.26          | ~ (v1_relat_1 @ X22))),
% 5.99/6.26      inference('cnf', [status(esa)], [t66_funct_1])).
% 5.99/6.26  thf('295', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 5.99/6.26          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('sup+', [status(thm)], ['293', '294'])).
% 5.99/6.26  thf('296', plain, (![X14 : $i]: (v1_relat_1 @ (k6_partfun1 @ X14))),
% 5.99/6.26      inference('demod', [status(thm)], ['93', '94'])).
% 5.99/6.26  thf('297', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('298', plain, (![X0 : $i]: (v2_funct_1 @ (k6_partfun1 @ X0))),
% 5.99/6.26      inference('simplify', [status(thm)], ['106'])).
% 5.99/6.26  thf('299', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (((k2_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26            = (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('demod', [status(thm)], ['295', '296', '297', '298'])).
% 5.99/6.26  thf('300', plain,
% 5.99/6.26      (![X13 : $i]:
% 5.99/6.26         ((v1_funct_1 @ (k2_funct_1 @ X13))
% 5.99/6.26          | ~ (v1_funct_1 @ X13)
% 5.99/6.26          | ~ (v1_relat_1 @ X13))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 5.99/6.26  thf('301', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         ((v1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ X1) @ (k6_partfun1 @ X0)))
% 5.99/6.26          | ~ (v1_relat_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v2_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))),
% 5.99/6.26      inference('sup+', [status(thm)], ['299', '300'])).
% 5.99/6.26  thf('302', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 5.99/6.26          | ~ (v2_funct_1 @ sk_D)
% 5.99/6.26          | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26          | ~ (v1_relat_1 @ sk_D)
% 5.99/6.26          | (v1_funct_1 @ 
% 5.99/6.26             (k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ X0))))),
% 5.99/6.26      inference('sup-', [status(thm)], ['292', '301'])).
% 5.99/6.26  thf('303', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('304', plain,
% 5.99/6.26      (![X37 : $i]:
% 5.99/6.26         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 5.99/6.26          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 5.99/6.26  thf('305', plain,
% 5.99/6.26      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 5.99/6.26          | ~ (v1_funct_1 @ X30)
% 5.99/6.26          | ~ (v1_funct_1 @ X33)
% 5.99/6.26          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 5.99/6.26          | (v1_funct_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33)))),
% 5.99/6.26      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 5.99/6.26  thf('306', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         ((v1_funct_1 @ 
% 5.99/6.26           (k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 5.99/6.26          | ~ (v1_funct_1 @ X1)
% 5.99/6.26          | ~ (v1_funct_1 @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['304', '305'])).
% 5.99/6.26  thf('307', plain, (![X15 : $i]: (v1_funct_1 @ (k6_partfun1 @ X15))),
% 5.99/6.26      inference('demod', [status(thm)], ['45', '46'])).
% 5.99/6.26  thf('308', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.99/6.26         ((v1_funct_1 @ 
% 5.99/6.26           (k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_partfun1 @ X0) @ X1))
% 5.99/6.26          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 5.99/6.26          | ~ (v1_funct_1 @ X1))),
% 5.99/6.26      inference('demod', [status(thm)], ['306', '307'])).
% 5.99/6.26  thf('309', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (v1_funct_1 @ sk_D)
% 5.99/6.26          | (v1_funct_1 @ 
% 5.99/6.26             (k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['303', '308'])).
% 5.99/6.26  thf('310', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('311', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (v1_funct_1 @ 
% 5.99/6.26          (k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['309', '310'])).
% 5.99/6.26  thf('312', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         ((k1_partfun1 @ X0 @ X0 @ sk_B @ sk_A @ (k6_partfun1 @ X0) @ sk_D)
% 5.99/6.26           = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['285', '286'])).
% 5.99/6.26  thf('313', plain,
% 5.99/6.26      (![X0 : $i]: (v1_funct_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['311', '312'])).
% 5.99/6.26  thf('314', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('315', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('316', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('317', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (v1_funct_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_D) @ (k6_partfun1 @ X0)))),
% 5.99/6.26      inference('demod', [status(thm)], ['302', '313', '314', '315', '316'])).
% 5.99/6.26  thf('318', plain,
% 5.99/6.26      (((v1_funct_1 @ (k2_funct_1 @ sk_D))
% 5.99/6.26        | ~ (v1_relat_1 @ sk_D)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26        | ~ (v2_funct_1 @ sk_D))),
% 5.99/6.26      inference('sup+', [status(thm)], ['269', '317'])).
% 5.99/6.26  thf('319', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('320', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('321', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('322', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['318', '319', '320', '321'])).
% 5.99/6.26  thf('323', plain,
% 5.99/6.26      ((((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (k1_relat_1 @ sk_D))
% 5.99/6.26        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 5.99/6.26        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['268', '322'])).
% 5.99/6.26  thf('324', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['248', '249', '250', '251', '252'])).
% 5.99/6.26  thf('325', plain,
% 5.99/6.26      ((((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (k1_relat_1 @ sk_D))
% 5.99/6.26        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('demod', [status(thm)], ['323', '324'])).
% 5.99/6.26  thf('326', plain,
% 5.99/6.26      ((~ (v1_relat_1 @ sk_D)
% 5.99/6.26        | ~ (v1_funct_1 @ sk_D)
% 5.99/6.26        | ~ (v2_funct_1 @ sk_D)
% 5.99/6.26        | ((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (k1_relat_1 @ sk_D)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['265', '325'])).
% 5.99/6.26  thf('327', plain, ((v1_relat_1 @ sk_D)),
% 5.99/6.26      inference('demod', [status(thm)], ['62', '63'])).
% 5.99/6.26  thf('328', plain, ((v1_funct_1 @ sk_D)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('329', plain, ((v2_funct_1 @ sk_D)),
% 5.99/6.26      inference('sup-', [status(thm)], ['117', '118'])).
% 5.99/6.26  thf('330', plain,
% 5.99/6.26      (((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (k1_relat_1 @ sk_D))),
% 5.99/6.26      inference('demod', [status(thm)], ['326', '327', '328', '329'])).
% 5.99/6.26  thf('331', plain,
% 5.99/6.26      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf(t31_funct_2, axiom,
% 5.99/6.26    (![A:$i,B:$i,C:$i]:
% 5.99/6.26     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 5.99/6.26         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 5.99/6.26       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 5.99/6.26         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 5.99/6.26           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 5.99/6.26           ( m1_subset_1 @
% 5.99/6.26             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 5.99/6.26  thf('332', plain,
% 5.99/6.26      (![X54 : $i, X55 : $i, X56 : $i]:
% 5.99/6.26         (~ (v2_funct_1 @ X54)
% 5.99/6.26          | ((k2_relset_1 @ X56 @ X55 @ X54) != (X55))
% 5.99/6.26          | (m1_subset_1 @ (k2_funct_1 @ X54) @ 
% 5.99/6.26             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X56)))
% 5.99/6.26          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X55)))
% 5.99/6.26          | ~ (v1_funct_2 @ X54 @ X56 @ X55)
% 5.99/6.26          | ~ (v1_funct_1 @ X54))),
% 5.99/6.26      inference('cnf', [status(esa)], [t31_funct_2])).
% 5.99/6.26  thf('333', plain,
% 5.99/6.26      ((~ (v1_funct_1 @ sk_C)
% 5.99/6.26        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 5.99/6.26        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.99/6.26           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.99/6.26        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 5.99/6.26        | ~ (v2_funct_1 @ sk_C))),
% 5.99/6.26      inference('sup-', [status(thm)], ['331', '332'])).
% 5.99/6.26  thf('334', plain, ((v1_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('335', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('336', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('337', plain, ((v2_funct_1 @ sk_C)),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('338', plain,
% 5.99/6.26      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.99/6.26         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 5.99/6.26        | ((sk_B) != (sk_B)))),
% 5.99/6.26      inference('demod', [status(thm)], ['333', '334', '335', '336', '337'])).
% 5.99/6.26  thf('339', plain,
% 5.99/6.26      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 5.99/6.26        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 5.99/6.26      inference('simplify', [status(thm)], ['338'])).
% 5.99/6.26  thf('340', plain,
% 5.99/6.26      (![X0 : $i, X1 : $i]:
% 5.99/6.26         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 5.99/6.26          | (v1_relat_1 @ X0)
% 5.99/6.26          | ~ (v1_relat_1 @ X1))),
% 5.99/6.26      inference('cnf', [status(esa)], [cc2_relat_1])).
% 5.99/6.26  thf('341', plain,
% 5.99/6.26      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))
% 5.99/6.26        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['339', '340'])).
% 5.99/6.26  thf('342', plain,
% 5.99/6.26      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 5.99/6.26      inference('cnf', [status(esa)], [fc6_relat_1])).
% 5.99/6.26  thf('343', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 5.99/6.26      inference('demod', [status(thm)], ['341', '342'])).
% 5.99/6.26  thf('344', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (((k6_partfun1 @ sk_A) != (k6_partfun1 @ sk_A))
% 5.99/6.26          | ((sk_C) = (k2_funct_1 @ sk_D))
% 5.99/6.26          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ X0))
% 5.99/6.26          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 5.99/6.26      inference('demod', [status(thm)],
% 5.99/6.26                ['193', '207', '208', '209', '210', '211', '212', '213', 
% 5.99/6.26                 '253', '264', '330', '343'])).
% 5.99/6.26  thf('345', plain,
% 5.99/6.26      (![X0 : $i]:
% 5.99/6.26         (~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 5.99/6.26          | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ X0))
% 5.99/6.26          | ((sk_C) = (k2_funct_1 @ sk_D)))),
% 5.99/6.26      inference('simplify', [status(thm)], ['344'])).
% 5.99/6.26  thf('346', plain,
% 5.99/6.26      ((((sk_C) = (k2_funct_1 @ sk_D))
% 5.99/6.26        | ((k6_partfun1 @ sk_B) != (k6_partfun1 @ sk_B)))),
% 5.99/6.26      inference('sup-', [status(thm)], ['146', '345'])).
% 5.99/6.26  thf('347', plain, (((sk_C) = (k2_funct_1 @ sk_D))),
% 5.99/6.26      inference('simplify', [status(thm)], ['346'])).
% 5.99/6.26  thf('348', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 5.99/6.26      inference('demod', [status(thm)], ['139', '347'])).
% 5.99/6.26  thf('349', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 5.99/6.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.99/6.26  thf('350', plain, ($false),
% 5.99/6.26      inference('simplify_reflect-', [status(thm)], ['348', '349'])).
% 5.99/6.26  
% 5.99/6.26  % SZS output end Refutation
% 5.99/6.26  
% 5.99/6.26  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
