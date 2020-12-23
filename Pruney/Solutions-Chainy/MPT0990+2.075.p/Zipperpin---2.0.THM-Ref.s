%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JYPP0EqEiK

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:06 EST 2020

% Result     : Theorem 39.95s
% Output     : Refutation 39.95s
% Verified   : 
% Statistics : Number of formulae       :  309 (2123 expanded)
%              Number of leaves         :   49 ( 641 expanded)
%              Depth                    :   34
%              Number of atoms          : 3281 (51944 expanded)
%              Number of equality atoms :  178 (3482 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('19',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('21',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

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

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('41',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('42',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('43',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_relat_1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','52','53','54'])).

thf('56',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('57',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('63',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['57','60'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('67',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['63','64','65','66'])).

thf('68',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['36','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('82',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('83',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
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

thf('86',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('93',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('94',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','95'])).

thf('97',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('98',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['80','98'])).

thf('100',plain,(
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

thf('101',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ( zip_tseitin_0 @ X44 @ X47 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44 ) )
      | ( zip_tseitin_1 @ X46 @ X45 )
      | ( ( k2_relset_1 @ X48 @ X45 @ X47 )
       != X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X48 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('108',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('111',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('115',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('116',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['113','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','123','124','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['111','112'])).

thf('128',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('129',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('131',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['131','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('135',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf(fc7_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A )
        & ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B )
        & ( v2_funct_1 @ B ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) )
        & ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ) )).

thf('137',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v2_funct_1 @ X8 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_funct_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['138','139','140','141'])).

thf('143',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['126','142'])).

thf('144',plain,(
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

thf('145',plain,(
    ! [X49: $i,X50: $i,X51: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_relset_1 @ X51 @ X50 @ X49 )
       != X50 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('146',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','123','124','125'])).

thf('154',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['120','123','124','125'])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['143','152','153','154'])).

thf('156',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['108','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['107','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['161','162','163','164'])).

thf('166',plain,(
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

thf('167',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_partfun1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('168',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('169',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_relat_1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['166','169'])).

thf('171',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['170','171','172','173','174'])).

thf('176',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['176','177'])).

thf('179',plain,(
    v2_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['165','178'])).

thf('180',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['106','179','180','181','182','183'])).

thf('185',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('187',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X40: $i,X41: $i] :
      ( ( v2_funct_1 @ X41 )
      | ~ ( zip_tseitin_0 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('191',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['71','191'])).

thf('193',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','52','53','54'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('195',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['193','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('197',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['195','196','197'])).

thf('199',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['189','190'])).

thf('200',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ( X52 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X52 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X52 ) ) )
      | ( ( k5_relat_1 @ X53 @ ( k2_funct_1 @ X53 ) )
        = ( k6_relat_1 @ X54 ) )
      | ~ ( v2_funct_1 @ X53 )
      | ( ( k2_relset_1 @ X54 @ X52 @ X53 )
       != X52 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('203',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','52','53','54'])).

thf('206',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['204','205'])).

thf('207',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['203','206','207','208'])).

thf('210',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['210','211'])).

thf('213',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['189','190'])).

thf('214',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['212','213'])).

thf('215',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('217',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['121','122'])).

thf('219',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['214','220'])).

thf('222',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['129','130'])).

thf('223',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['48','51','52','53','54'])).

thf('224',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('225',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('226',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('229',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('230',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('231',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('232',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['230','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['229','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['228','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['227','239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['226','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['225','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['224','244'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['223','246'])).

thf('248',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['57','60'])).

thf('249',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['58','59'])).

thf('250',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['247','248','249','250'])).

thf('252',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['189','190'])).

thf('253',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['251','252'])).

thf('254',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['221','222','253'])).

thf('255',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference('sup+',[status(thm)],['200','254'])).

thf('256',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['192','255'])).

thf('257',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['256','257'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JYPP0EqEiK
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:26:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 39.95/40.17  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 39.95/40.17  % Solved by: fo/fo7.sh
% 39.95/40.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 39.95/40.17  % done 7859 iterations in 39.702s
% 39.95/40.17  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 39.95/40.17  % SZS output start Refutation
% 39.95/40.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 39.95/40.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 39.95/40.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 39.95/40.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 39.95/40.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 39.95/40.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 39.95/40.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 39.95/40.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 39.95/40.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 39.95/40.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 39.95/40.17  thf(sk_C_type, type, sk_C: $i).
% 39.95/40.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 39.95/40.17  thf(sk_B_type, type, sk_B: $i).
% 39.95/40.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 39.95/40.17  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 39.95/40.17  thf(sk_A_type, type, sk_A: $i).
% 39.95/40.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 39.95/40.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 39.95/40.17  thf(sk_D_type, type, sk_D: $i).
% 39.95/40.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 39.95/40.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 39.95/40.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 39.95/40.17  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 39.95/40.17  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 39.95/40.17  thf(t80_relat_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( v1_relat_1 @ A ) =>
% 39.95/40.17       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 39.95/40.17  thf('0', plain,
% 39.95/40.17      (![X4 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 39.95/40.17          | ~ (v1_relat_1 @ X4))),
% 39.95/40.17      inference('cnf', [status(esa)], [t80_relat_1])).
% 39.95/40.17  thf(t78_relat_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( v1_relat_1 @ A ) =>
% 39.95/40.17       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 39.95/40.17  thf('1', plain,
% 39.95/40.17      (![X3 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 39.95/40.17          | ~ (v1_relat_1 @ X3))),
% 39.95/40.17      inference('cnf', [status(esa)], [t78_relat_1])).
% 39.95/40.17  thf(t55_relat_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( v1_relat_1 @ A ) =>
% 39.95/40.17       ( ![B:$i]:
% 39.95/40.17         ( ( v1_relat_1 @ B ) =>
% 39.95/40.17           ( ![C:$i]:
% 39.95/40.17             ( ( v1_relat_1 @ C ) =>
% 39.95/40.17               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 39.95/40.17                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 39.95/40.17  thf('2', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 39.95/40.17              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 39.95/40.17          | ~ (v1_relat_1 @ X2)
% 39.95/40.17          | ~ (v1_relat_1 @ X1))),
% 39.95/40.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 39.95/40.17  thf('3', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ X1)
% 39.95/40.17            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 39.95/40.17               (k5_relat_1 @ X0 @ X1)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X1)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('sup+', [status(thm)], ['1', '2'])).
% 39.95/40.17  thf('4', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X1)
% 39.95/40.17          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ X1)
% 39.95/40.17              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 39.95/40.17                 (k5_relat_1 @ X0 @ X1))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['3'])).
% 39.95/40.17  thf(dt_k6_partfun1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( m1_subset_1 @
% 39.95/40.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 39.95/40.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 39.95/40.17  thf('5', plain,
% 39.95/40.17      (![X28 : $i]:
% 39.95/40.17         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 39.95/40.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 39.95/40.17  thf(redefinition_k6_partfun1, axiom,
% 39.95/40.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 39.95/40.17  thf('6', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 39.95/40.17  thf('7', plain,
% 39.95/40.17      (![X28 : $i]:
% 39.95/40.17         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 39.95/40.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 39.95/40.17      inference('demod', [status(thm)], ['5', '6'])).
% 39.95/40.17  thf(cc1_relset_1, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i]:
% 39.95/40.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.95/40.17       ( v1_relat_1 @ C ) ))).
% 39.95/40.17  thf('8', plain,
% 39.95/40.17      (![X11 : $i, X12 : $i, X13 : $i]:
% 39.95/40.17         ((v1_relat_1 @ X11)
% 39.95/40.17          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 39.95/40.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 39.95/40.17  thf('9', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 39.95/40.17      inference('sup-', [status(thm)], ['7', '8'])).
% 39.95/40.17  thf('10', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X1)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ X1)
% 39.95/40.17              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 39.95/40.17                 (k5_relat_1 @ X0 @ X1))))),
% 39.95/40.17      inference('demod', [status(thm)], ['4', '9'])).
% 39.95/40.17  thf('11', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 39.95/40.17      inference('sup+', [status(thm)], ['0', '10'])).
% 39.95/40.17  thf('12', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 39.95/40.17      inference('sup-', [status(thm)], ['7', '8'])).
% 39.95/40.17  thf('13', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('demod', [status(thm)], ['11', '12'])).
% 39.95/40.17  thf('14', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 39.95/40.17      inference('simplify', [status(thm)], ['13'])).
% 39.95/40.17  thf(t55_funct_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 39.95/40.17       ( ( v2_funct_1 @ A ) =>
% 39.95/40.17         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 39.95/40.17           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 39.95/40.17  thf('15', plain,
% 39.95/40.17      (![X9 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X9)
% 39.95/40.17          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 39.95/40.17          | ~ (v1_funct_1 @ X9)
% 39.95/40.17          | ~ (v1_relat_1 @ X9))),
% 39.95/40.17      inference('cnf', [status(esa)], [t55_funct_1])).
% 39.95/40.17  thf(fc6_funct_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 39.95/40.17       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 39.95/40.17         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 39.95/40.17         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 39.95/40.17  thf('16', plain,
% 39.95/40.17      (![X6 : $i]:
% 39.95/40.17         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 39.95/40.17          | ~ (v2_funct_1 @ X6)
% 39.95/40.17          | ~ (v1_funct_1 @ X6)
% 39.95/40.17          | ~ (v1_relat_1 @ X6))),
% 39.95/40.17      inference('cnf', [status(esa)], [fc6_funct_1])).
% 39.95/40.17  thf(dt_k2_funct_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 39.95/40.17       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 39.95/40.17         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 39.95/40.17  thf('17', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('18', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf(t65_funct_1, axiom,
% 39.95/40.17    (![A:$i]:
% 39.95/40.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 39.95/40.17       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 39.95/40.17  thf('19', plain,
% 39.95/40.17      (![X10 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X10)
% 39.95/40.17          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 39.95/40.17          | ~ (v1_funct_1 @ X10)
% 39.95/40.17          | ~ (v1_relat_1 @ X10))),
% 39.95/40.17      inference('cnf', [status(esa)], [t65_funct_1])).
% 39.95/40.17  thf('20', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('21', plain,
% 39.95/40.17      (![X9 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X9)
% 39.95/40.17          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 39.95/40.17          | ~ (v1_funct_1 @ X9)
% 39.95/40.17          | ~ (v1_relat_1 @ X9))),
% 39.95/40.17      inference('cnf', [status(esa)], [t55_funct_1])).
% 39.95/40.17  thf('22', plain,
% 39.95/40.17      (![X4 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 39.95/40.17          | ~ (v1_relat_1 @ X4))),
% 39.95/40.17      inference('cnf', [status(esa)], [t80_relat_1])).
% 39.95/40.17  thf('23', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 39.95/40.17            = (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['21', '22'])).
% 39.95/40.17  thf('24', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 39.95/40.17              = (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['20', '23'])).
% 39.95/40.17  thf('25', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 39.95/40.17            = (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['24'])).
% 39.95/40.17  thf('26', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['19', '25'])).
% 39.95/40.17  thf('27', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['18', '26'])).
% 39.95/40.17  thf('28', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['27'])).
% 39.95/40.17  thf('29', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['17', '28'])).
% 39.95/40.17  thf('30', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['29'])).
% 39.95/40.17  thf('31', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['16', '30'])).
% 39.95/40.17  thf('32', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 39.95/40.17            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['31'])).
% 39.95/40.17  thf('33', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0))),
% 39.95/40.17      inference('sup+', [status(thm)], ['15', '32'])).
% 39.95/40.17  thf('34', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['33'])).
% 39.95/40.17  thf('35', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)
% 39.95/40.17            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0))),
% 39.95/40.17      inference('sup+', [status(thm)], ['14', '34'])).
% 39.95/40.17  thf('36', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['35'])).
% 39.95/40.17  thf(t36_funct_2, conjecture,
% 39.95/40.17    (![A:$i,B:$i,C:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 39.95/40.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17       ( ![D:$i]:
% 39.95/40.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 39.95/40.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 39.95/40.17           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 39.95/40.17               ( r2_relset_1 @
% 39.95/40.17                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 39.95/40.17                 ( k6_partfun1 @ A ) ) & 
% 39.95/40.17               ( v2_funct_1 @ C ) ) =>
% 39.95/40.17             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 39.95/40.17               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 39.95/40.17  thf(zf_stmt_0, negated_conjecture,
% 39.95/40.17    (~( ![A:$i,B:$i,C:$i]:
% 39.95/40.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 39.95/40.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17          ( ![D:$i]:
% 39.95/40.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 39.95/40.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 39.95/40.17              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 39.95/40.17                  ( r2_relset_1 @
% 39.95/40.17                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 39.95/40.17                    ( k6_partfun1 @ A ) ) & 
% 39.95/40.17                  ( v2_funct_1 @ C ) ) =>
% 39.95/40.17                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 39.95/40.17                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 39.95/40.17    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 39.95/40.17  thf('37', plain,
% 39.95/40.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 39.95/40.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 39.95/40.17        (k6_partfun1 @ sk_A))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('38', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 39.95/40.17  thf('39', plain,
% 39.95/40.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 39.95/40.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 39.95/40.17        (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['37', '38'])).
% 39.95/40.17  thf('40', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(t24_funct_2, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 39.95/40.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17       ( ![D:$i]:
% 39.95/40.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 39.95/40.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 39.95/40.17           ( ( r2_relset_1 @
% 39.95/40.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 39.95/40.17               ( k6_partfun1 @ B ) ) =>
% 39.95/40.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 39.95/40.17  thf('41', plain,
% 39.95/40.17      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X36)
% 39.95/40.17          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 39.95/40.17          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 39.95/40.17          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 39.95/40.17               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 39.95/40.17               (k6_partfun1 @ X37))
% 39.95/40.17          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 39.95/40.17          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 39.95/40.17          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 39.95/40.17          | ~ (v1_funct_1 @ X39))),
% 39.95/40.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 39.95/40.17  thf('42', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 39.95/40.17  thf('43', plain,
% 39.95/40.17      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X36)
% 39.95/40.17          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 39.95/40.17          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 39.95/40.17          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 39.95/40.17               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 39.95/40.17               (k6_relat_1 @ X37))
% 39.95/40.17          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 39.95/40.17          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 39.95/40.17          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 39.95/40.17          | ~ (v1_funct_1 @ X39))),
% 39.95/40.17      inference('demod', [status(thm)], ['41', '42'])).
% 39.95/40.17  thf('44', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 39.95/40.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 39.95/40.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 39.95/40.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 39.95/40.17               (k6_relat_1 @ sk_A))
% 39.95/40.17          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 39.95/40.17          | ~ (v1_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup-', [status(thm)], ['40', '43'])).
% 39.95/40.17  thf('45', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('47', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 39.95/40.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 39.95/40.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 39.95/40.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 39.95/40.17               (k6_relat_1 @ sk_A)))),
% 39.95/40.17      inference('demod', [status(thm)], ['44', '45', '46'])).
% 39.95/40.17  thf('48', plain,
% 39.95/40.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 39.95/40.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 39.95/40.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_D))),
% 39.95/40.17      inference('sup-', [status(thm)], ['39', '47'])).
% 39.95/40.17  thf('49', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(redefinition_k2_relset_1, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i]:
% 39.95/40.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 39.95/40.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 39.95/40.17  thf('50', plain,
% 39.95/40.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 39.95/40.17         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 39.95/40.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 39.95/40.17  thf('51', plain,
% 39.95/40.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 39.95/40.17      inference('sup-', [status(thm)], ['49', '50'])).
% 39.95/40.17  thf('52', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('53', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('55', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['48', '51', '52', '53', '54'])).
% 39.95/40.17  thf('56', plain,
% 39.95/40.17      (![X4 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 39.95/40.17          | ~ (v1_relat_1 @ X4))),
% 39.95/40.17      inference('cnf', [status(esa)], [t80_relat_1])).
% 39.95/40.17  thf('57', plain,
% 39.95/40.17      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_D))),
% 39.95/40.17      inference('sup+', [status(thm)], ['55', '56'])).
% 39.95/40.17  thf('58', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('59', plain,
% 39.95/40.17      (![X11 : $i, X12 : $i, X13 : $i]:
% 39.95/40.17         ((v1_relat_1 @ X11)
% 39.95/40.17          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 39.95/40.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 39.95/40.17  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['58', '59'])).
% 39.95/40.17  thf('61', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['57', '60'])).
% 39.95/40.17  thf('62', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X1)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ X1)
% 39.95/40.17              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 39.95/40.17                 (k5_relat_1 @ X0 @ X1))))),
% 39.95/40.17      inference('demod', [status(thm)], ['4', '9'])).
% 39.95/40.17  thf('63', plain,
% 39.95/40.17      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A))
% 39.95/40.17          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_D)
% 39.95/40.17        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['61', '62'])).
% 39.95/40.17  thf('64', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['57', '60'])).
% 39.95/40.17  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['58', '59'])).
% 39.95/40.17  thf('66', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 39.95/40.17      inference('sup-', [status(thm)], ['7', '8'])).
% 39.95/40.17  thf('67', plain,
% 39.95/40.17      (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['63', '64', '65', '66'])).
% 39.95/40.17  thf('68', plain,
% 39.95/40.17      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_D)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_D)
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('sup+', [status(thm)], ['36', '67'])).
% 39.95/40.17  thf('69', plain, ((v1_relat_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['58', '59'])).
% 39.95/40.17  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('71', plain,
% 39.95/40.17      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))) | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['68', '69', '70'])).
% 39.95/40.17  thf('72', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('73', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(redefinition_k1_partfun1, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ E ) & 
% 39.95/40.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 39.95/40.17         ( v1_funct_1 @ F ) & 
% 39.95/40.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 39.95/40.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 39.95/40.17  thf('74', plain,
% 39.95/40.17      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 39.95/40.17         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 39.95/40.17          | ~ (v1_funct_1 @ X29)
% 39.95/40.17          | ~ (v1_funct_1 @ X32)
% 39.95/40.17          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 39.95/40.17          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 39.95/40.17              = (k5_relat_1 @ X29 @ X32)))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 39.95/40.17  thf('75', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ X0))
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup-', [status(thm)], ['73', '74'])).
% 39.95/40.17  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('77', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ X0))
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 39.95/40.17          | ~ (v1_funct_1 @ X0))),
% 39.95/40.17      inference('demod', [status(thm)], ['75', '76'])).
% 39.95/40.17  thf('78', plain,
% 39.95/40.17      ((~ (v1_funct_1 @ sk_D)
% 39.95/40.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ sk_D)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['72', '77'])).
% 39.95/40.17  thf('79', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('80', plain,
% 39.95/40.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 39.95/40.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['78', '79'])).
% 39.95/40.17  thf('81', plain,
% 39.95/40.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 39.95/40.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 39.95/40.17        (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['37', '38'])).
% 39.95/40.17  thf('82', plain,
% 39.95/40.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 39.95/40.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['78', '79'])).
% 39.95/40.17  thf('83', plain,
% 39.95/40.17      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 39.95/40.17        (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['81', '82'])).
% 39.95/40.17  thf('84', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('85', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(dt_k1_partfun1, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ E ) & 
% 39.95/40.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 39.95/40.17         ( v1_funct_1 @ F ) & 
% 39.95/40.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 39.95/40.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 39.95/40.17         ( m1_subset_1 @
% 39.95/40.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 39.95/40.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 39.95/40.17  thf('86', plain,
% 39.95/40.17      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 39.95/40.17         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 39.95/40.17          | ~ (v1_funct_1 @ X21)
% 39.95/40.17          | ~ (v1_funct_1 @ X24)
% 39.95/40.17          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 39.95/40.17          | (m1_subset_1 @ (k1_partfun1 @ X22 @ X23 @ X25 @ X26 @ X21 @ X24) @ 
% 39.95/40.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X26))))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 39.95/40.17  thf('87', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 39.95/40.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 39.95/40.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 39.95/40.17          | ~ (v1_funct_1 @ X1)
% 39.95/40.17          | ~ (v1_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup-', [status(thm)], ['85', '86'])).
% 39.95/40.17  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('89', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 39.95/40.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 39.95/40.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 39.95/40.17          | ~ (v1_funct_1 @ X1))),
% 39.95/40.17      inference('demod', [status(thm)], ['87', '88'])).
% 39.95/40.17  thf('90', plain,
% 39.95/40.17      ((~ (v1_funct_1 @ sk_D)
% 39.95/40.17        | (m1_subset_1 @ 
% 39.95/40.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 39.95/40.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['84', '89'])).
% 39.95/40.17  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('92', plain,
% 39.95/40.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 39.95/40.17         = (k5_relat_1 @ sk_C @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['78', '79'])).
% 39.95/40.17  thf('93', plain,
% 39.95/40.17      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 39.95/40.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 39.95/40.17      inference('demod', [status(thm)], ['90', '91', '92'])).
% 39.95/40.17  thf(redefinition_r2_relset_1, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i,D:$i]:
% 39.95/40.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 39.95/40.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 39.95/40.17  thf('94', plain,
% 39.95/40.17      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 39.95/40.17         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 39.95/40.17          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 39.95/40.17          | ((X17) = (X20))
% 39.95/40.17          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 39.95/40.17  thf('95', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 39.95/40.17          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['93', '94'])).
% 39.95/40.17  thf('96', plain,
% 39.95/40.17      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 39.95/40.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 39.95/40.17        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['83', '95'])).
% 39.95/40.17  thf('97', plain,
% 39.95/40.17      (![X28 : $i]:
% 39.95/40.17         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 39.95/40.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 39.95/40.17      inference('demod', [status(thm)], ['5', '6'])).
% 39.95/40.17  thf('98', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['96', '97'])).
% 39.95/40.17  thf('99', plain,
% 39.95/40.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 39.95/40.17         = (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['80', '98'])).
% 39.95/40.17  thf('100', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(t30_funct_2, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i,D:$i]:
% 39.95/40.17     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 39.95/40.17         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 39.95/40.17       ( ![E:$i]:
% 39.95/40.17         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 39.95/40.17             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 39.95/40.17           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 39.95/40.17               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 39.95/40.17             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 39.95/40.17               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 39.95/40.17  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 39.95/40.17  thf(zf_stmt_2, axiom,
% 39.95/40.17    (![C:$i,B:$i]:
% 39.95/40.17     ( ( zip_tseitin_1 @ C @ B ) =>
% 39.95/40.17       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 39.95/40.17  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 39.95/40.17  thf(zf_stmt_4, axiom,
% 39.95/40.17    (![E:$i,D:$i]:
% 39.95/40.17     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 39.95/40.17  thf(zf_stmt_5, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i,D:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 39.95/40.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17       ( ![E:$i]:
% 39.95/40.17         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 39.95/40.17             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 39.95/40.17           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 39.95/40.17               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 39.95/40.17             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 39.95/40.17  thf('101', plain,
% 39.95/40.17      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X44)
% 39.95/40.17          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 39.95/40.17          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 39.95/40.17          | (zip_tseitin_0 @ X44 @ X47)
% 39.95/40.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X45 @ X45 @ X46 @ X47 @ X44))
% 39.95/40.17          | (zip_tseitin_1 @ X46 @ X45)
% 39.95/40.17          | ((k2_relset_1 @ X48 @ X45 @ X47) != (X45))
% 39.95/40.17          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X45)))
% 39.95/40.17          | ~ (v1_funct_2 @ X47 @ X48 @ X45)
% 39.95/40.17          | ~ (v1_funct_1 @ X47))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_5])).
% 39.95/40.17  thf('102', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 39.95/40.17          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 39.95/40.17          | (zip_tseitin_1 @ sk_A @ sk_B)
% 39.95/40.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 39.95/40.17          | (zip_tseitin_0 @ sk_D @ X0)
% 39.95/40.17          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 39.95/40.17          | ~ (v1_funct_1 @ sk_D))),
% 39.95/40.17      inference('sup-', [status(thm)], ['100', '101'])).
% 39.95/40.17  thf('103', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('104', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('105', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i]:
% 39.95/40.17         (~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 39.95/40.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 39.95/40.17          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 39.95/40.17          | (zip_tseitin_1 @ sk_A @ sk_B)
% 39.95/40.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 39.95/40.17          | (zip_tseitin_0 @ sk_D @ X0))),
% 39.95/40.17      inference('demod', [status(thm)], ['102', '103', '104'])).
% 39.95/40.17  thf('106', plain,
% 39.95/40.17      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 39.95/40.17        | (zip_tseitin_0 @ sk_D @ sk_C)
% 39.95/40.17        | (zip_tseitin_1 @ sk_A @ sk_B)
% 39.95/40.17        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 39.95/40.17        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 39.95/40.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup-', [status(thm)], ['99', '105'])).
% 39.95/40.17  thf('107', plain,
% 39.95/40.17      (![X6 : $i]:
% 39.95/40.17         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 39.95/40.17          | ~ (v2_funct_1 @ X6)
% 39.95/40.17          | ~ (v1_funct_1 @ X6)
% 39.95/40.17          | ~ (v1_relat_1 @ X6))),
% 39.95/40.17      inference('cnf', [status(esa)], [fc6_funct_1])).
% 39.95/40.17  thf('108', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('109', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('110', plain,
% 39.95/40.17      (![X14 : $i, X15 : $i, X16 : $i]:
% 39.95/40.17         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 39.95/40.17          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 39.95/40.17  thf('111', plain,
% 39.95/40.17      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 39.95/40.17      inference('sup-', [status(thm)], ['109', '110'])).
% 39.95/40.17  thf('112', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('113', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 39.95/40.17      inference('sup+', [status(thm)], ['111', '112'])).
% 39.95/40.17  thf('114', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('115', plain,
% 39.95/40.17      (![X9 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X9)
% 39.95/40.17          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 39.95/40.17          | ~ (v1_funct_1 @ X9)
% 39.95/40.17          | ~ (v1_relat_1 @ X9))),
% 39.95/40.17      inference('cnf', [status(esa)], [t55_funct_1])).
% 39.95/40.17  thf('116', plain,
% 39.95/40.17      (![X3 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 39.95/40.17          | ~ (v1_relat_1 @ X3))),
% 39.95/40.17      inference('cnf', [status(esa)], [t78_relat_1])).
% 39.95/40.17  thf('117', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 39.95/40.17            = (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['115', '116'])).
% 39.95/40.17  thf('118', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 39.95/40.17              = (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['114', '117'])).
% 39.95/40.17  thf('119', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 39.95/40.17            = (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['118'])).
% 39.95/40.17  thf('120', plain,
% 39.95/40.17      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 39.95/40.17          = (k2_funct_1 @ sk_C))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_C)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_C)
% 39.95/40.17        | ~ (v2_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup+', [status(thm)], ['113', '119'])).
% 39.95/40.17  thf('121', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('122', plain,
% 39.95/40.17      (![X11 : $i, X12 : $i, X13 : $i]:
% 39.95/40.17         ((v1_relat_1 @ X11)
% 39.95/40.17          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 39.95/40.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 39.95/40.17  thf('123', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('126', plain,
% 39.95/40.17      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 39.95/40.17         = (k2_funct_1 @ sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['120', '123', '124', '125'])).
% 39.95/40.17  thf('127', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 39.95/40.17      inference('sup+', [status(thm)], ['111', '112'])).
% 39.95/40.17  thf('128', plain,
% 39.95/40.17      (![X4 : $i]:
% 39.95/40.17         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 39.95/40.17          | ~ (v1_relat_1 @ X4))),
% 39.95/40.17      inference('cnf', [status(esa)], [t80_relat_1])).
% 39.95/40.17  thf('129', plain,
% 39.95/40.17      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_C))),
% 39.95/40.17      inference('sup+', [status(thm)], ['127', '128'])).
% 39.95/40.17  thf('130', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('131', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['129', '130'])).
% 39.95/40.17  thf('132', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 39.95/40.17              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 39.95/40.17          | ~ (v1_relat_1 @ X2)
% 39.95/40.17          | ~ (v1_relat_1 @ X1))),
% 39.95/40.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 39.95/40.17  thf('133', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ sk_C @ X0)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ sk_C)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['131', '132'])).
% 39.95/40.17  thf('134', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('135', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 39.95/40.17      inference('sup-', [status(thm)], ['7', '8'])).
% 39.95/40.17  thf('136', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ sk_C @ X0)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('demod', [status(thm)], ['133', '134', '135'])).
% 39.95/40.17  thf(fc7_funct_1, axiom,
% 39.95/40.17    (![A:$i,B:$i]:
% 39.95/40.17     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) & 
% 39.95/40.17         ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v2_funct_1 @ B ) ) =>
% 39.95/40.17       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 39.95/40.17         ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 39.95/40.17  thf('137', plain,
% 39.95/40.17      (![X7 : $i, X8 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X7)
% 39.95/40.17          | ~ (v1_funct_1 @ X7)
% 39.95/40.17          | ~ (v1_relat_1 @ X7)
% 39.95/40.17          | ~ (v1_relat_1 @ X8)
% 39.95/40.17          | ~ (v1_funct_1 @ X8)
% 39.95/40.17          | ~ (v2_funct_1 @ X8)
% 39.95/40.17          | (v2_funct_1 @ (k5_relat_1 @ X7 @ X8)))),
% 39.95/40.17      inference('cnf', [status(esa)], [fc7_funct_1])).
% 39.95/40.17  thf('138', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v2_funct_1 @ (k5_relat_1 @ sk_C @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ sk_C)
% 39.95/40.17          | ~ (v1_funct_1 @ sk_C)
% 39.95/40.17          | ~ (v2_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup+', [status(thm)], ['136', '137'])).
% 39.95/40.17  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('142', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v2_funct_1 @ (k5_relat_1 @ sk_C @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)))),
% 39.95/40.17      inference('demod', [status(thm)], ['138', '139', '140', '141'])).
% 39.95/40.17  thf('143', plain,
% 39.95/40.17      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | ~ (v1_relat_1 @ 
% 39.95/40.17             (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 39.95/40.17        | ~ (v2_funct_1 @ 
% 39.95/40.17             (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 39.95/40.17        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['126', '142'])).
% 39.95/40.17  thf('144', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(t31_funct_2, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 39.95/40.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 39.95/40.17         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 39.95/40.17           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 39.95/40.17           ( m1_subset_1 @
% 39.95/40.17             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 39.95/40.17  thf('145', plain,
% 39.95/40.17      (![X49 : $i, X50 : $i, X51 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X49)
% 39.95/40.17          | ((k2_relset_1 @ X51 @ X50 @ X49) != (X50))
% 39.95/40.17          | (v1_funct_1 @ (k2_funct_1 @ X49))
% 39.95/40.17          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 39.95/40.17          | ~ (v1_funct_2 @ X49 @ X51 @ X50)
% 39.95/40.17          | ~ (v1_funct_1 @ X49))),
% 39.95/40.17      inference('cnf', [status(esa)], [t31_funct_2])).
% 39.95/40.17  thf('146', plain,
% 39.95/40.17      ((~ (v1_funct_1 @ sk_C)
% 39.95/40.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 39.95/40.17        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_C))),
% 39.95/40.17      inference('sup-', [status(thm)], ['144', '145'])).
% 39.95/40.17  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('148', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('149', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('151', plain,
% 39.95/40.17      (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 39.95/40.17      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 39.95/40.17  thf('152', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 39.95/40.17      inference('simplify', [status(thm)], ['151'])).
% 39.95/40.17  thf('153', plain,
% 39.95/40.17      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 39.95/40.17         = (k2_funct_1 @ sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['120', '123', '124', '125'])).
% 39.95/40.17  thf('154', plain,
% 39.95/40.17      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 39.95/40.17         = (k2_funct_1 @ sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['120', '123', '124', '125'])).
% 39.95/40.17  thf('155', plain,
% 39.95/40.17      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 39.95/40.17      inference('demod', [status(thm)], ['143', '152', '153', '154'])).
% 39.95/40.17  thf('156', plain,
% 39.95/40.17      (((v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 39.95/40.17        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 39.95/40.17      inference('simplify', [status(thm)], ['155'])).
% 39.95/40.17  thf('157', plain,
% 39.95/40.17      ((~ (v1_relat_1 @ sk_C)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_C)
% 39.95/40.17        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['108', '156'])).
% 39.95/40.17  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('160', plain,
% 39.95/40.17      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 39.95/40.17        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 39.95/40.17      inference('demod', [status(thm)], ['157', '158', '159'])).
% 39.95/40.17  thf('161', plain,
% 39.95/40.17      ((~ (v1_relat_1 @ sk_C)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_C)
% 39.95/40.17        | ~ (v2_funct_1 @ sk_C)
% 39.95/40.17        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['107', '160'])).
% 39.95/40.17  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('164', plain, ((v2_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('165', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 39.95/40.17      inference('demod', [status(thm)], ['161', '162', '163', '164'])).
% 39.95/40.17  thf('166', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf(t35_funct_2, axiom,
% 39.95/40.17    (![A:$i,B:$i,C:$i]:
% 39.95/40.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 39.95/40.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 39.95/40.17       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 39.95/40.17         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 39.95/40.17           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 39.95/40.17             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 39.95/40.17  thf('167', plain,
% 39.95/40.17      (![X52 : $i, X53 : $i, X54 : $i]:
% 39.95/40.17         (((X52) = (k1_xboole_0))
% 39.95/40.17          | ~ (v1_funct_1 @ X53)
% 39.95/40.17          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 39.95/40.17          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 39.95/40.17          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_partfun1 @ X54))
% 39.95/40.17          | ~ (v2_funct_1 @ X53)
% 39.95/40.17          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 39.95/40.17      inference('cnf', [status(esa)], [t35_funct_2])).
% 39.95/40.17  thf('168', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 39.95/40.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 39.95/40.17  thf('169', plain,
% 39.95/40.17      (![X52 : $i, X53 : $i, X54 : $i]:
% 39.95/40.17         (((X52) = (k1_xboole_0))
% 39.95/40.17          | ~ (v1_funct_1 @ X53)
% 39.95/40.17          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 39.95/40.17          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 39.95/40.17          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 39.95/40.17          | ~ (v2_funct_1 @ X53)
% 39.95/40.17          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 39.95/40.17      inference('demod', [status(thm)], ['167', '168'])).
% 39.95/40.17  thf('170', plain,
% 39.95/40.17      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_C)
% 39.95/40.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 39.95/40.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_C)
% 39.95/40.17        | ((sk_B) = (k1_xboole_0)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['166', '169'])).
% 39.95/40.17  thf('171', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('172', plain, ((v2_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('173', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('175', plain,
% 39.95/40.17      ((((sk_B) != (sk_B))
% 39.95/40.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 39.95/40.17        | ((sk_B) = (k1_xboole_0)))),
% 39.95/40.17      inference('demod', [status(thm)], ['170', '171', '172', '173', '174'])).
% 39.95/40.17  thf('176', plain,
% 39.95/40.17      ((((sk_B) = (k1_xboole_0))
% 39.95/40.17        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 39.95/40.17      inference('simplify', [status(thm)], ['175'])).
% 39.95/40.17  thf('177', plain, (((sk_B) != (k1_xboole_0))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('178', plain,
% 39.95/40.17      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('simplify_reflect-', [status(thm)], ['176', '177'])).
% 39.95/40.17  thf('179', plain, ((v2_funct_1 @ (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['165', '178'])).
% 39.95/40.17  thf('180', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('181', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('182', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('184', plain,
% 39.95/40.17      (((zip_tseitin_0 @ sk_D @ sk_C)
% 39.95/40.17        | (zip_tseitin_1 @ sk_A @ sk_B)
% 39.95/40.17        | ((sk_B) != (sk_B)))),
% 39.95/40.17      inference('demod', [status(thm)],
% 39.95/40.17                ['106', '179', '180', '181', '182', '183'])).
% 39.95/40.17  thf('185', plain,
% 39.95/40.17      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 39.95/40.17      inference('simplify', [status(thm)], ['184'])).
% 39.95/40.17  thf('186', plain,
% 39.95/40.17      (![X42 : $i, X43 : $i]:
% 39.95/40.17         (((X42) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X42 @ X43))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_2])).
% 39.95/40.17  thf('187', plain,
% 39.95/40.17      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['185', '186'])).
% 39.95/40.17  thf('188', plain, (((sk_A) != (k1_xboole_0))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('189', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 39.95/40.17      inference('simplify_reflect-', [status(thm)], ['187', '188'])).
% 39.95/40.17  thf('190', plain,
% 39.95/40.17      (![X40 : $i, X41 : $i]:
% 39.95/40.17         ((v2_funct_1 @ X41) | ~ (zip_tseitin_0 @ X41 @ X40))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_4])).
% 39.95/40.17  thf('191', plain, ((v2_funct_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['189', '190'])).
% 39.95/40.17  thf('192', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 39.95/40.17      inference('demod', [status(thm)], ['71', '191'])).
% 39.95/40.17  thf('193', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['48', '51', '52', '53', '54'])).
% 39.95/40.17  thf('194', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 39.95/40.17            = (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['118'])).
% 39.95/40.17  thf('195', plain,
% 39.95/40.17      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 39.95/40.17          = (k2_funct_1 @ sk_D))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_D)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_D)
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('sup+', [status(thm)], ['193', '194'])).
% 39.95/40.17  thf('196', plain, ((v1_relat_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['58', '59'])).
% 39.95/40.17  thf('197', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('198', plain,
% 39.95/40.17      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 39.95/40.17          = (k2_funct_1 @ sk_D))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['195', '196', '197'])).
% 39.95/40.17  thf('199', plain, ((v2_funct_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['189', '190'])).
% 39.95/40.17  thf('200', plain,
% 39.95/40.17      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 39.95/40.17         = (k2_funct_1 @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['198', '199'])).
% 39.95/40.17  thf('201', plain,
% 39.95/40.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('202', plain,
% 39.95/40.17      (![X52 : $i, X53 : $i, X54 : $i]:
% 39.95/40.17         (((X52) = (k1_xboole_0))
% 39.95/40.17          | ~ (v1_funct_1 @ X53)
% 39.95/40.17          | ~ (v1_funct_2 @ X53 @ X54 @ X52)
% 39.95/40.17          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X52)))
% 39.95/40.17          | ((k5_relat_1 @ X53 @ (k2_funct_1 @ X53)) = (k6_relat_1 @ X54))
% 39.95/40.17          | ~ (v2_funct_1 @ X53)
% 39.95/40.17          | ((k2_relset_1 @ X54 @ X52 @ X53) != (X52)))),
% 39.95/40.17      inference('demod', [status(thm)], ['167', '168'])).
% 39.95/40.17  thf('203', plain,
% 39.95/40.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D)
% 39.95/40.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 39.95/40.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_D)
% 39.95/40.17        | ((sk_A) = (k1_xboole_0)))),
% 39.95/40.17      inference('sup-', [status(thm)], ['201', '202'])).
% 39.95/40.17  thf('204', plain,
% 39.95/40.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 39.95/40.17      inference('sup-', [status(thm)], ['49', '50'])).
% 39.95/40.17  thf('205', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['48', '51', '52', '53', '54'])).
% 39.95/40.17  thf('206', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['204', '205'])).
% 39.95/40.17  thf('207', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('208', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('209', plain,
% 39.95/40.17      ((((sk_A) != (sk_A))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D)
% 39.95/40.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 39.95/40.17        | ((sk_A) = (k1_xboole_0)))),
% 39.95/40.17      inference('demod', [status(thm)], ['203', '206', '207', '208'])).
% 39.95/40.17  thf('210', plain,
% 39.95/40.17      ((((sk_A) = (k1_xboole_0))
% 39.95/40.17        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('simplify', [status(thm)], ['209'])).
% 39.95/40.17  thf('211', plain, (((sk_A) != (k1_xboole_0))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('212', plain,
% 39.95/40.17      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('simplify_reflect-', [status(thm)], ['210', '211'])).
% 39.95/40.17  thf('213', plain, ((v2_funct_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['189', '190'])).
% 39.95/40.17  thf('214', plain,
% 39.95/40.17      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 39.95/40.17      inference('demod', [status(thm)], ['212', '213'])).
% 39.95/40.17  thf('215', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['96', '97'])).
% 39.95/40.17  thf('216', plain,
% 39.95/40.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 39.95/40.17              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 39.95/40.17          | ~ (v1_relat_1 @ X2)
% 39.95/40.17          | ~ (v1_relat_1 @ X1))),
% 39.95/40.17      inference('cnf', [status(esa)], [t55_relat_1])).
% 39.95/40.17  thf('217', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ sk_C)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ sk_D))),
% 39.95/40.17      inference('sup+', [status(thm)], ['215', '216'])).
% 39.95/40.17  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 39.95/40.17      inference('sup-', [status(thm)], ['121', '122'])).
% 39.95/40.17  thf('219', plain, ((v1_relat_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['58', '59'])).
% 39.95/40.17  thf('220', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 39.95/40.17            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('demod', [status(thm)], ['217', '218', '219'])).
% 39.95/40.17  thf('221', plain,
% 39.95/40.17      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 39.95/40.17          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 39.95/40.17        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['214', '220'])).
% 39.95/40.17  thf('222', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['129', '130'])).
% 39.95/40.17  thf('223', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 39.95/40.17      inference('demod', [status(thm)], ['48', '51', '52', '53', '54'])).
% 39.95/40.17  thf('224', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('225', plain,
% 39.95/40.17      (![X6 : $i]:
% 39.95/40.17         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 39.95/40.17          | ~ (v2_funct_1 @ X6)
% 39.95/40.17          | ~ (v1_funct_1 @ X6)
% 39.95/40.17          | ~ (v1_relat_1 @ X6))),
% 39.95/40.17      inference('cnf', [status(esa)], [fc6_funct_1])).
% 39.95/40.17  thf('226', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('227', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['33'])).
% 39.95/40.17  thf('228', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['33'])).
% 39.95/40.17  thf('229', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('230', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('231', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 39.95/40.17              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['33'])).
% 39.95/40.17  thf('232', plain,
% 39.95/40.17      (![X5 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 39.95/40.17          | ~ (v1_funct_1 @ X5)
% 39.95/40.17          | ~ (v1_relat_1 @ X5))),
% 39.95/40.17      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 39.95/40.17  thf('233', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['231', '232'])).
% 39.95/40.17  thf('234', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['230', '233'])).
% 39.95/40.17  thf('235', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['234'])).
% 39.95/40.17  thf('236', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['229', '235'])).
% 39.95/40.17  thf('237', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['236'])).
% 39.95/40.17  thf('238', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0))),
% 39.95/40.17      inference('sup+', [status(thm)], ['228', '237'])).
% 39.95/40.17  thf('239', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 39.95/40.17      inference('simplify', [status(thm)], ['238'])).
% 39.95/40.17  thf('240', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ 
% 39.95/40.17           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 39.95/40.17      inference('sup+', [status(thm)], ['227', '239'])).
% 39.95/40.17  thf('241', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | (v1_relat_1 @ 
% 39.95/40.17             (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['226', '240'])).
% 39.95/40.17  thf('242', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ 
% 39.95/40.17           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['241'])).
% 39.95/40.17  thf('243', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | (v1_relat_1 @ 
% 39.95/40.17             (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['225', '242'])).
% 39.95/40.17  thf('244', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ 
% 39.95/40.17           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 39.95/40.17          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['243'])).
% 39.95/40.17  thf('245', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         (~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | (v1_relat_1 @ 
% 39.95/40.17             (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 39.95/40.17      inference('sup-', [status(thm)], ['224', '244'])).
% 39.95/40.17  thf('246', plain,
% 39.95/40.17      (![X0 : $i]:
% 39.95/40.17         ((v1_relat_1 @ 
% 39.95/40.17           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 39.95/40.17          | ~ (v2_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_funct_1 @ X0)
% 39.95/40.17          | ~ (v1_relat_1 @ X0))),
% 39.95/40.17      inference('simplify', [status(thm)], ['245'])).
% 39.95/40.17  thf('247', plain,
% 39.95/40.17      (((v1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A))))
% 39.95/40.17        | ~ (v1_relat_1 @ sk_D)
% 39.95/40.17        | ~ (v1_funct_1 @ sk_D)
% 39.95/40.17        | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('sup+', [status(thm)], ['223', '246'])).
% 39.95/40.17  thf('248', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['57', '60'])).
% 39.95/40.17  thf('249', plain, ((v1_relat_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['58', '59'])).
% 39.95/40.17  thf('250', plain, ((v1_funct_1 @ sk_D)),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('251', plain,
% 39.95/40.17      (((v1_relat_1 @ (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['247', '248', '249', '250'])).
% 39.95/40.17  thf('252', plain, ((v2_funct_1 @ sk_D)),
% 39.95/40.17      inference('sup-', [status(thm)], ['189', '190'])).
% 39.95/40.17  thf('253', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 39.95/40.17      inference('demod', [status(thm)], ['251', '252'])).
% 39.95/40.17  thf('254', plain,
% 39.95/40.17      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['221', '222', '253'])).
% 39.95/40.17  thf('255', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 39.95/40.17      inference('sup+', [status(thm)], ['200', '254'])).
% 39.95/40.17  thf('256', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 39.95/40.17      inference('demod', [status(thm)], ['192', '255'])).
% 39.95/40.17  thf('257', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 39.95/40.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 39.95/40.17  thf('258', plain, ($false),
% 39.95/40.17      inference('simplify_reflect-', [status(thm)], ['256', '257'])).
% 39.95/40.17  
% 39.95/40.17  % SZS output end Refutation
% 39.95/40.17  
% 39.95/40.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
