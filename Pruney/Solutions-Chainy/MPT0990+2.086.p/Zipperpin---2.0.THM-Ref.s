%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.emkMKKuYTn

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:08 EST 2020

% Result     : Theorem 32.11s
% Output     : Refutation 32.11s
% Verified   : 
% Statistics : Number of formulae       :  306 (2083 expanded)
%              Number of leaves         :   48 ( 627 expanded)
%              Depth                    :   34
%              Number of atoms          : 3265 (51671 expanded)
%              Number of equality atoms :  177 (3456 expanded)
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

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

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

thf('1',plain,(
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

thf('2',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X10 ) )
        = X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('5',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','10'])).

thf('12',plain,(
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
    inference('sup-',[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
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

thf('21',plain,(
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

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X0 ) )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

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

thf('35',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('36',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_partfun1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('40',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( r2_relset_1 @ X36 @ X36 @ ( k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38 ) @ ( k6_relat_1 @ X36 ) )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('48',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('54',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('55',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('61',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
      = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['55','58'])).

thf('63',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('64',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('65',plain,
    ( sk_D
    = ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_D ) ) @ sk_D ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['34','65'])).

thf('67',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_D
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
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

thf('72',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 )
        = ( k5_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('80',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
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

thf('84',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('91',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('92',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','93'])).

thf('95',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('96',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['78','96'])).

thf('98',plain,(
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

thf('99',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( zip_tseitin_0 @ X43 @ X46 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43 ) )
      | ( zip_tseitin_1 @ X45 @ X44 )
      | ( ( k2_relset_1 @ X47 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('100',plain,(
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
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X1 @ sk_B @ X0 )
       != sk_B )
      | ( zip_tseitin_1 @ sk_A @ sk_B )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ( zip_tseitin_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('106',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('109',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('113',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k2_relat_1 @ X9 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('114',plain,(
    ! [X3: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) @ X3 )
        = X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['112','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['111','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','121','122','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['109','110'])).

thf('126',plain,(
    ! [X4: $i] :
      ( ( ( k5_relat_1 @ X4 @ ( k6_relat_1 @ ( k2_relat_1 @ X4 ) ) )
        = X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('127',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('129',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('133',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132','133'])).

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

thf('135',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v2_funct_1 @ X8 )
      | ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc7_funct_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['136','137','138','139'])).

thf('141',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['124','140'])).

thf('142',plain,(
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

thf('143',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( v2_funct_1 @ X48 )
      | ( ( k2_relset_1 @ X50 @ X49 @ X48 )
       != X49 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X48 ) )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X49 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X50 @ X49 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('144',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['144','145','146','147','148'])).

thf('150',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','121','122','123'])).

thf('152',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['118','121','122','123'])).

thf('153',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['141','150','151','152'])).

thf('154',plain,
    ( ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['106','154'])).

thf('156',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['105','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('161',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_funct_1 @ ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,(
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

thf('165',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_partfun1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('166',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('167',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['168','169','170','171','172'])).

thf('174',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['174','175'])).

thf('177',plain,(
    v2_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['163','176'])).

thf('178',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['104','177','178','179','180','181'])).

thf('183',plain,
    ( ( zip_tseitin_1 @ sk_A @ sk_B )
    | ( zip_tseitin_0 @ sk_D @ sk_C ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ! [X41: $i,X42: $i] :
      ( ( X41 = k1_xboole_0 )
      | ~ ( zip_tseitin_1 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('185',plain,
    ( ( zip_tseitin_0 @ sk_D @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    zip_tseitin_0 @ sk_D @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['185','186'])).

thf('188',plain,(
    ! [X39: $i,X40: $i] :
      ( ( v2_funct_1 @ X40 )
      | ~ ( zip_tseitin_0 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('189',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,
    ( sk_D
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['69','189'])).

thf('191',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('193',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('195',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['187','188'])).

thf('198',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( X51 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X51 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X51 ) ) )
      | ( ( k5_relat_1 @ X52 @ ( k2_funct_1 @ X52 ) )
        = ( k6_relat_1 @ X53 ) )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X53 @ X51 @ X52 )
       != X51 ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('201',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('204',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['202','203'])).

thf('205',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( sk_A != sk_A )
    | ~ ( v2_funct_1 @ sk_D )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['201','204','205','206'])).

thf('208',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['208','209'])).

thf('211',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['187','188'])).

thf('212',plain,
    ( ( k5_relat_1 @ sk_D @ ( k2_funct_1 @ sk_D ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('214',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['119','120'])).

thf('217',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ X0 )
        = ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ sk_D @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['212','218'])).

thf('220',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['127','128'])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['46','49','50','51','52'])).

thf('222',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('223',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X6 ) )
      | ~ ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('224',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('227',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('228',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('229',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('230',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['229','230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['228','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['227','233'])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['226','235'])).

thf('237',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['225','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['224','238'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['239'])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['223','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['222','242'])).

thf('244',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ X0 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['243'])).

thf('245',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['221','244'])).

thf('246',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_relat_1 @ sk_A ) )
    = sk_D ),
    inference(demod,[status(thm)],['55','58'])).

thf('247',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['56','57'])).

thf('248',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['245','246','247','248'])).

thf('250',plain,(
    v2_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['187','188'])).

thf('251',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_D ) ),
    inference(demod,[status(thm)],['249','250'])).

thf('252',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ ( k2_funct_1 @ sk_D ) )
    = sk_C ),
    inference(demod,[status(thm)],['219','220','251'])).

thf('253',plain,
    ( ( k2_funct_1 @ sk_D )
    = sk_C ),
    inference('sup+',[status(thm)],['198','252'])).

thf('254',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','253'])).

thf('255',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['254','255'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.emkMKKuYTn
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 32.11/32.33  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 32.11/32.33  % Solved by: fo/fo7.sh
% 32.11/32.33  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 32.11/32.33  % done 6906 iterations in 31.865s
% 32.11/32.33  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 32.11/32.33  % SZS output start Refutation
% 32.11/32.33  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 32.11/32.33  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 32.11/32.33  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 32.11/32.33  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 32.11/32.33  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 32.11/32.33  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 32.11/32.33  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 32.11/32.33  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 32.11/32.33  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 32.11/32.33  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 32.11/32.33  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 32.11/32.33  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 32.11/32.33  thf(sk_D_type, type, sk_D: $i).
% 32.11/32.33  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 32.11/32.33  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 32.11/32.33  thf(sk_C_type, type, sk_C: $i).
% 32.11/32.33  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 32.11/32.33  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 32.11/32.33  thf(sk_A_type, type, sk_A: $i).
% 32.11/32.33  thf(sk_B_type, type, sk_B: $i).
% 32.11/32.33  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 32.11/32.33  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 32.11/32.33  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 32.11/32.33  thf(t55_funct_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.11/32.33       ( ( v2_funct_1 @ A ) =>
% 32.11/32.33         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 32.11/32.33           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 32.11/32.33  thf('0', plain,
% 32.11/32.33      (![X9 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X9)
% 32.11/32.33          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 32.11/32.33          | ~ (v1_funct_1 @ X9)
% 32.11/32.33          | ~ (v1_relat_1 @ X9))),
% 32.11/32.33      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.11/32.33  thf(fc6_funct_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 32.11/32.33       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 32.11/32.33         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 32.11/32.33         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 32.11/32.33  thf('1', plain,
% 32.11/32.33      (![X6 : $i]:
% 32.11/32.33         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 32.11/32.33          | ~ (v2_funct_1 @ X6)
% 32.11/32.33          | ~ (v1_funct_1 @ X6)
% 32.11/32.33          | ~ (v1_relat_1 @ X6))),
% 32.11/32.33      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.11/32.33  thf(dt_k2_funct_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.11/32.33       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 32.11/32.33         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 32.11/32.33  thf('2', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('3', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf(t65_funct_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 32.11/32.33       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 32.11/32.33  thf('4', plain,
% 32.11/32.33      (![X10 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X10)
% 32.11/32.33          | ((k2_funct_1 @ (k2_funct_1 @ X10)) = (X10))
% 32.11/32.33          | ~ (v1_funct_1 @ X10)
% 32.11/32.33          | ~ (v1_relat_1 @ X10))),
% 32.11/32.33      inference('cnf', [status(esa)], [t65_funct_1])).
% 32.11/32.33  thf('5', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('6', plain,
% 32.11/32.33      (![X9 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X9)
% 32.11/32.33          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 32.11/32.33          | ~ (v1_funct_1 @ X9)
% 32.11/32.33          | ~ (v1_relat_1 @ X9))),
% 32.11/32.33      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.11/32.33  thf(t80_relat_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( v1_relat_1 @ A ) =>
% 32.11/32.33       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 32.11/32.33  thf('7', plain,
% 32.11/32.33      (![X4 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 32.11/32.33          | ~ (v1_relat_1 @ X4))),
% 32.11/32.33      inference('cnf', [status(esa)], [t80_relat_1])).
% 32.11/32.33  thf('8', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.11/32.33            = (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['6', '7'])).
% 32.11/32.33  thf('9', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.11/32.33              = (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['5', '8'])).
% 32.11/32.33  thf('10', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.11/32.33            = (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['9'])).
% 32.11/32.33  thf('11', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['4', '10'])).
% 32.11/32.33  thf('12', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['3', '11'])).
% 32.11/32.33  thf('13', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['12'])).
% 32.11/32.33  thf('14', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['2', '13'])).
% 32.11/32.33  thf('15', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['14'])).
% 32.11/32.33  thf('16', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['1', '15'])).
% 32.11/32.33  thf('17', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 32.11/32.33            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['16'])).
% 32.11/32.33  thf('18', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33            = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0))),
% 32.11/32.33      inference('sup+', [status(thm)], ['0', '17'])).
% 32.11/32.33  thf('19', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('simplify', [status(thm)], ['18'])).
% 32.11/32.33  thf('20', plain,
% 32.11/32.33      (![X4 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 32.11/32.33          | ~ (v1_relat_1 @ X4))),
% 32.11/32.33      inference('cnf', [status(esa)], [t80_relat_1])).
% 32.11/32.33  thf(t78_relat_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( v1_relat_1 @ A ) =>
% 32.11/32.33       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 32.11/32.33  thf('21', plain,
% 32.11/32.33      (![X3 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 32.11/32.33          | ~ (v1_relat_1 @ X3))),
% 32.11/32.33      inference('cnf', [status(esa)], [t78_relat_1])).
% 32.11/32.33  thf(t55_relat_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( ( v1_relat_1 @ A ) =>
% 32.11/32.33       ( ![B:$i]:
% 32.11/32.33         ( ( v1_relat_1 @ B ) =>
% 32.11/32.33           ( ![C:$i]:
% 32.11/32.33             ( ( v1_relat_1 @ C ) =>
% 32.11/32.33               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 32.11/32.33                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 32.11/32.33  thf('22', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 32.11/32.33              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 32.11/32.33          | ~ (v1_relat_1 @ X2)
% 32.11/32.33          | ~ (v1_relat_1 @ X1))),
% 32.11/32.33      inference('cnf', [status(esa)], [t55_relat_1])).
% 32.11/32.33  thf('23', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ X1)
% 32.11/32.33            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 32.11/32.33               (k5_relat_1 @ X0 @ X1)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X1)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('sup+', [status(thm)], ['21', '22'])).
% 32.11/32.33  thf('24', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X1)
% 32.11/32.33          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ X1)
% 32.11/32.33              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 32.11/32.33                 (k5_relat_1 @ X0 @ X1))))),
% 32.11/32.33      inference('simplify', [status(thm)], ['23'])).
% 32.11/32.33  thf(t29_relset_1, axiom,
% 32.11/32.33    (![A:$i]:
% 32.11/32.33     ( m1_subset_1 @
% 32.11/32.33       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 32.11/32.33  thf('25', plain,
% 32.11/32.33      (![X21 : $i]:
% 32.11/32.33         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 32.11/32.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 32.11/32.33      inference('cnf', [status(esa)], [t29_relset_1])).
% 32.11/32.33  thf(cc1_relset_1, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i]:
% 32.11/32.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.11/32.33       ( v1_relat_1 @ C ) ))).
% 32.11/32.33  thf('26', plain,
% 32.11/32.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.11/32.33         ((v1_relat_1 @ X11)
% 32.11/32.33          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 32.11/32.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.11/32.33  thf('27', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 32.11/32.33      inference('sup-', [status(thm)], ['25', '26'])).
% 32.11/32.33  thf('28', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X1)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ X1)
% 32.11/32.33              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 32.11/32.33                 (k5_relat_1 @ X0 @ X1))))),
% 32.11/32.33      inference('demod', [status(thm)], ['24', '27'])).
% 32.11/32.33  thf('29', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0))))),
% 32.11/32.33      inference('sup+', [status(thm)], ['20', '28'])).
% 32.11/32.33  thf('30', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 32.11/32.33      inference('sup-', [status(thm)], ['25', '26'])).
% 32.11/32.33  thf('31', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('demod', [status(thm)], ['29', '30'])).
% 32.11/32.33  thf('32', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 32.11/32.33      inference('simplify', [status(thm)], ['31'])).
% 32.11/32.33  thf('33', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33            = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('sup+', [status(thm)], ['19', '32'])).
% 32.11/32.33  thf('34', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0)))),
% 32.11/32.33      inference('simplify', [status(thm)], ['33'])).
% 32.11/32.33  thf(t36_funct_2, conjecture,
% 32.11/32.33    (![A:$i,B:$i,C:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.11/32.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33       ( ![D:$i]:
% 32.11/32.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 32.11/32.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 32.11/32.33           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 32.11/32.33               ( r2_relset_1 @
% 32.11/32.33                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 32.11/32.33                 ( k6_partfun1 @ A ) ) & 
% 32.11/32.33               ( v2_funct_1 @ C ) ) =>
% 32.11/32.33             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.11/32.33               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 32.11/32.33  thf(zf_stmt_0, negated_conjecture,
% 32.11/32.33    (~( ![A:$i,B:$i,C:$i]:
% 32.11/32.33        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.11/32.33            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33          ( ![D:$i]:
% 32.11/32.33            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 32.11/32.33                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 32.11/32.33              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 32.11/32.33                  ( r2_relset_1 @
% 32.11/32.33                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 32.11/32.33                    ( k6_partfun1 @ A ) ) & 
% 32.11/32.33                  ( v2_funct_1 @ C ) ) =>
% 32.11/32.33                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.11/32.33                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 32.11/32.33    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 32.11/32.33  thf('35', plain,
% 32.11/32.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 32.11/32.33        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.11/32.33        (k6_partfun1 @ sk_A))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(redefinition_k6_partfun1, axiom,
% 32.11/32.33    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 32.11/32.33  thf('36', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.11/32.33  thf('37', plain,
% 32.11/32.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 32.11/32.33        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.11/32.33        (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['35', '36'])).
% 32.11/32.33  thf('38', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(t24_funct_2, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.11/32.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33       ( ![D:$i]:
% 32.11/32.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 32.11/32.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 32.11/32.33           ( ( r2_relset_1 @
% 32.11/32.33               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 32.11/32.33               ( k6_partfun1 @ B ) ) =>
% 32.11/32.33             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 32.11/32.33  thf('39', plain,
% 32.11/32.33      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X35)
% 32.11/32.33          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 32.11/32.33          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 32.11/32.33          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 32.11/32.33               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 32.11/32.33               (k6_partfun1 @ X36))
% 32.11/32.33          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 32.11/32.33          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 32.11/32.33          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 32.11/32.33          | ~ (v1_funct_1 @ X38))),
% 32.11/32.33      inference('cnf', [status(esa)], [t24_funct_2])).
% 32.11/32.33  thf('40', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.11/32.33  thf('41', plain,
% 32.11/32.33      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X35)
% 32.11/32.33          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 32.11/32.33          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 32.11/32.33          | ~ (r2_relset_1 @ X36 @ X36 @ 
% 32.11/32.33               (k1_partfun1 @ X36 @ X37 @ X37 @ X36 @ X35 @ X38) @ 
% 32.11/32.33               (k6_relat_1 @ X36))
% 32.11/32.33          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 32.11/32.33          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 32.11/32.33          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 32.11/32.33          | ~ (v1_funct_1 @ X38))),
% 32.11/32.33      inference('demod', [status(thm)], ['39', '40'])).
% 32.11/32.33  thf('42', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 32.11/32.33          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 32.11/32.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 32.11/32.33               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 32.11/32.33               (k6_relat_1 @ sk_A))
% 32.11/32.33          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.11/32.33          | ~ (v1_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup-', [status(thm)], ['38', '41'])).
% 32.11/32.33  thf('43', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('45', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 32.11/32.33          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 32.11/32.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 32.11/32.33               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 32.11/32.33               (k6_relat_1 @ sk_A)))),
% 32.11/32.33      inference('demod', [status(thm)], ['42', '43', '44'])).
% 32.11/32.33  thf('46', plain,
% 32.11/32.33      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 32.11/32.33        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 32.11/32.33        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_D))),
% 32.11/32.33      inference('sup-', [status(thm)], ['37', '45'])).
% 32.11/32.33  thf('47', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(redefinition_k2_relset_1, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i]:
% 32.11/32.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 32.11/32.33       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 32.11/32.33  thf('48', plain,
% 32.11/32.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 32.11/32.33         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 32.11/32.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.11/32.33  thf('49', plain,
% 32.11/32.33      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 32.11/32.33      inference('sup-', [status(thm)], ['47', '48'])).
% 32.11/32.33  thf('50', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('51', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('53', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 32.11/32.33  thf('54', plain,
% 32.11/32.33      (![X4 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 32.11/32.33          | ~ (v1_relat_1 @ X4))),
% 32.11/32.33      inference('cnf', [status(esa)], [t80_relat_1])).
% 32.11/32.33  thf('55', plain,
% 32.11/32.33      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_D))),
% 32.11/32.33      inference('sup+', [status(thm)], ['53', '54'])).
% 32.11/32.33  thf('56', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('57', plain,
% 32.11/32.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.11/32.33         ((v1_relat_1 @ X11)
% 32.11/32.33          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 32.11/32.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.11/32.33  thf('58', plain, ((v1_relat_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['56', '57'])).
% 32.11/32.33  thf('59', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['55', '58'])).
% 32.11/32.33  thf('60', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X1)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ X1)
% 32.11/32.33              = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ 
% 32.11/32.33                 (k5_relat_1 @ X0 @ X1))))),
% 32.11/32.33      inference('demod', [status(thm)], ['24', '27'])).
% 32.11/32.33  thf('61', plain,
% 32.11/32.33      ((((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A))
% 32.11/32.33          = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_D)
% 32.11/32.33        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['59', '60'])).
% 32.11/32.33  thf('62', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['55', '58'])).
% 32.11/32.33  thf('63', plain, ((v1_relat_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['56', '57'])).
% 32.11/32.33  thf('64', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 32.11/32.33      inference('sup-', [status(thm)], ['25', '26'])).
% 32.11/32.33  thf('65', plain,
% 32.11/32.33      (((sk_D) = (k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_D)) @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 32.11/32.33  thf('66', plain,
% 32.11/32.33      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_D)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_D)
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('sup+', [status(thm)], ['34', '65'])).
% 32.11/32.33  thf('67', plain, ((v1_relat_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['56', '57'])).
% 32.11/32.33  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('69', plain,
% 32.11/32.33      ((((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D))) | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['66', '67', '68'])).
% 32.11/32.33  thf('70', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('71', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(redefinition_k1_partfun1, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ E ) & 
% 32.11/32.33         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.11/32.33         ( v1_funct_1 @ F ) & 
% 32.11/32.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 32.11/32.33       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 32.11/32.33  thf('72', plain,
% 32.11/32.33      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 32.11/32.33         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 32.11/32.33          | ~ (v1_funct_1 @ X28)
% 32.11/32.33          | ~ (v1_funct_1 @ X31)
% 32.11/32.33          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 32.11/32.33          | ((k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)
% 32.11/32.33              = (k5_relat_1 @ X28 @ X31)))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 32.11/32.33  thf('73', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ X0))
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup-', [status(thm)], ['71', '72'])).
% 32.11/32.33  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('75', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ X0))
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 32.11/32.33          | ~ (v1_funct_1 @ X0))),
% 32.11/32.33      inference('demod', [status(thm)], ['73', '74'])).
% 32.11/32.33  thf('76', plain,
% 32.11/32.33      ((~ (v1_funct_1 @ sk_D)
% 32.11/32.33        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ sk_D)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['70', '75'])).
% 32.11/32.33  thf('77', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('78', plain,
% 32.11/32.33      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.11/32.33         = (k5_relat_1 @ sk_C @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['76', '77'])).
% 32.11/32.33  thf('79', plain,
% 32.11/32.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 32.11/32.33        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.11/32.33        (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['35', '36'])).
% 32.11/32.33  thf('80', plain,
% 32.11/32.33      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.11/32.33         = (k5_relat_1 @ sk_C @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['76', '77'])).
% 32.11/32.33  thf('81', plain,
% 32.11/32.33      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 32.11/32.33        (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['79', '80'])).
% 32.11/32.33  thf('82', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('83', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(dt_k1_partfun1, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ E ) & 
% 32.11/32.33         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.11/32.33         ( v1_funct_1 @ F ) & 
% 32.11/32.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 32.11/32.33       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 32.11/32.33         ( m1_subset_1 @
% 32.11/32.33           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 32.11/32.33           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 32.11/32.33  thf('84', plain,
% 32.11/32.33      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 32.11/32.33         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 32.11/32.33          | ~ (v1_funct_1 @ X22)
% 32.11/32.33          | ~ (v1_funct_1 @ X25)
% 32.11/32.33          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 32.11/32.33          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 32.11/32.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 32.11/32.33  thf('85', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 32.11/32.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 32.11/32.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 32.11/32.33          | ~ (v1_funct_1 @ X1)
% 32.11/32.33          | ~ (v1_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup-', [status(thm)], ['83', '84'])).
% 32.11/32.33  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('87', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 32.11/32.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 32.11/32.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 32.11/32.33          | ~ (v1_funct_1 @ X1))),
% 32.11/32.33      inference('demod', [status(thm)], ['85', '86'])).
% 32.11/32.33  thf('88', plain,
% 32.11/32.33      ((~ (v1_funct_1 @ sk_D)
% 32.11/32.33        | (m1_subset_1 @ 
% 32.11/32.33           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 32.11/32.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['82', '87'])).
% 32.11/32.33  thf('89', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('90', plain,
% 32.11/32.33      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.11/32.33         = (k5_relat_1 @ sk_C @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['76', '77'])).
% 32.11/32.33  thf('91', plain,
% 32.11/32.33      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 32.11/32.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 32.11/32.33      inference('demod', [status(thm)], ['88', '89', '90'])).
% 32.11/32.33  thf(redefinition_r2_relset_1, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i,D:$i]:
% 32.11/32.33     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.11/32.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 32.11/32.33  thf('92', plain,
% 32.11/32.33      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 32.11/32.33         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 32.11/32.33          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 32.11/32.33          | ((X17) = (X20))
% 32.11/32.33          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 32.11/32.33  thf('93', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 32.11/32.33          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['91', '92'])).
% 32.11/32.33  thf('94', plain,
% 32.11/32.33      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 32.11/32.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 32.11/32.33        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['81', '93'])).
% 32.11/32.33  thf('95', plain,
% 32.11/32.33      (![X21 : $i]:
% 32.11/32.33         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 32.11/32.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 32.11/32.33      inference('cnf', [status(esa)], [t29_relset_1])).
% 32.11/32.33  thf('96', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['94', '95'])).
% 32.11/32.33  thf('97', plain,
% 32.11/32.33      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 32.11/32.33         = (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['78', '96'])).
% 32.11/32.33  thf('98', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(t30_funct_2, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i,D:$i]:
% 32.11/32.33     ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 32.11/32.33         ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 32.11/32.33       ( ![E:$i]:
% 32.11/32.33         ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) & 
% 32.11/32.33             ( v1_funct_2 @ E @ B @ C ) & ( v1_funct_1 @ E ) ) =>
% 32.11/32.33           ( ( ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) & 
% 32.11/32.33               ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) ) =>
% 32.11/32.33             ( ( ( v2_funct_1 @ E ) & ( v2_funct_1 @ D ) ) | 
% 32.11/32.33               ( ( ( B ) != ( k1_xboole_0 ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ))).
% 32.11/32.33  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $o).
% 32.11/32.33  thf(zf_stmt_2, axiom,
% 32.11/32.33    (![C:$i,B:$i]:
% 32.11/32.33     ( ( zip_tseitin_1 @ C @ B ) =>
% 32.11/32.33       ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ))).
% 32.11/32.33  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 32.11/32.33  thf(zf_stmt_4, axiom,
% 32.11/32.33    (![E:$i,D:$i]:
% 32.11/32.33     ( ( zip_tseitin_0 @ E @ D ) => ( ( v2_funct_1 @ D ) & ( v2_funct_1 @ E ) ) ))).
% 32.11/32.33  thf(zf_stmt_5, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i,D:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 32.11/32.33         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33       ( ![E:$i]:
% 32.11/32.33         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 32.11/32.33             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 32.11/32.33           ( ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) & 
% 32.11/32.33               ( ( k2_relset_1 @ A @ B @ D ) = ( B ) ) ) =>
% 32.11/32.33             ( ( zip_tseitin_1 @ C @ B ) | ( zip_tseitin_0 @ E @ D ) ) ) ) ) ))).
% 32.11/32.33  thf('99', plain,
% 32.11/32.33      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X43)
% 32.11/32.33          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 32.11/32.33          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 32.11/32.33          | (zip_tseitin_0 @ X43 @ X46)
% 32.11/32.33          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X44 @ X44 @ X45 @ X46 @ X43))
% 32.11/32.33          | (zip_tseitin_1 @ X45 @ X44)
% 32.11/32.33          | ((k2_relset_1 @ X47 @ X44 @ X46) != (X44))
% 32.11/32.33          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X44)))
% 32.11/32.33          | ~ (v1_funct_2 @ X46 @ X47 @ X44)
% 32.11/32.33          | ~ (v1_funct_1 @ X46))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_5])).
% 32.11/32.33  thf('100', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 32.11/32.33          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 32.11/32.33          | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.11/32.33          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 32.11/32.33          | (zip_tseitin_0 @ sk_D @ X0)
% 32.11/32.33          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 32.11/32.33          | ~ (v1_funct_1 @ sk_D))),
% 32.11/32.33      inference('sup-', [status(thm)], ['98', '99'])).
% 32.11/32.33  thf('101', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('102', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('103', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i]:
% 32.11/32.33         (~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 32.11/32.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 32.11/32.33          | ((k2_relset_1 @ X1 @ sk_B @ X0) != (sk_B))
% 32.11/32.33          | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.11/32.33          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 32.11/32.33          | (zip_tseitin_0 @ sk_D @ X0))),
% 32.11/32.33      inference('demod', [status(thm)], ['100', '101', '102'])).
% 32.11/32.33  thf('104', plain,
% 32.11/32.33      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 32.11/32.33        | (zip_tseitin_0 @ sk_D @ sk_C)
% 32.11/32.33        | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.11/32.33        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 32.11/32.33        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 32.11/32.33        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup-', [status(thm)], ['97', '103'])).
% 32.11/32.33  thf('105', plain,
% 32.11/32.33      (![X6 : $i]:
% 32.11/32.33         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 32.11/32.33          | ~ (v2_funct_1 @ X6)
% 32.11/32.33          | ~ (v1_funct_1 @ X6)
% 32.11/32.33          | ~ (v1_relat_1 @ X6))),
% 32.11/32.33      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.11/32.33  thf('106', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('107', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('108', plain,
% 32.11/32.33      (![X14 : $i, X15 : $i, X16 : $i]:
% 32.11/32.33         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 32.11/32.33          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 32.11/32.33  thf('109', plain,
% 32.11/32.33      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 32.11/32.33      inference('sup-', [status(thm)], ['107', '108'])).
% 32.11/32.33  thf('110', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('111', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 32.11/32.33      inference('sup+', [status(thm)], ['109', '110'])).
% 32.11/32.33  thf('112', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('113', plain,
% 32.11/32.33      (![X9 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X9)
% 32.11/32.33          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 32.11/32.33          | ~ (v1_funct_1 @ X9)
% 32.11/32.33          | ~ (v1_relat_1 @ X9))),
% 32.11/32.33      inference('cnf', [status(esa)], [t55_funct_1])).
% 32.11/32.33  thf('114', plain,
% 32.11/32.33      (![X3 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X3)) @ X3) = (X3))
% 32.11/32.33          | ~ (v1_relat_1 @ X3))),
% 32.11/32.33      inference('cnf', [status(esa)], [t78_relat_1])).
% 32.11/32.33  thf('115', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.11/32.33            = (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['113', '114'])).
% 32.11/32.33  thf('116', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.11/32.33              = (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['112', '115'])).
% 32.11/32.33  thf('117', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.11/32.33            = (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['116'])).
% 32.11/32.33  thf('118', plain,
% 32.11/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.11/32.33          = (k2_funct_1 @ sk_C))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_C)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.11/32.33        | ~ (v2_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup+', [status(thm)], ['111', '117'])).
% 32.11/32.33  thf('119', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('120', plain,
% 32.11/32.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 32.11/32.33         ((v1_relat_1 @ X11)
% 32.11/32.33          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 32.11/32.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 32.11/32.33  thf('121', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('123', plain, ((v2_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('124', plain,
% 32.11/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.11/32.33         = (k2_funct_1 @ sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['118', '121', '122', '123'])).
% 32.11/32.33  thf('125', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 32.11/32.33      inference('sup+', [status(thm)], ['109', '110'])).
% 32.11/32.33  thf('126', plain,
% 32.11/32.33      (![X4 : $i]:
% 32.11/32.33         (((k5_relat_1 @ X4 @ (k6_relat_1 @ (k2_relat_1 @ X4))) = (X4))
% 32.11/32.33          | ~ (v1_relat_1 @ X4))),
% 32.11/32.33      inference('cnf', [status(esa)], [t80_relat_1])).
% 32.11/32.33  thf('127', plain,
% 32.11/32.33      ((((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_C))),
% 32.11/32.33      inference('sup+', [status(thm)], ['125', '126'])).
% 32.11/32.33  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('129', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['127', '128'])).
% 32.11/32.33  thf('130', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 32.11/32.33              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 32.11/32.33          | ~ (v1_relat_1 @ X2)
% 32.11/32.33          | ~ (v1_relat_1 @ X1))),
% 32.11/32.33      inference('cnf', [status(esa)], [t55_relat_1])).
% 32.11/32.33  thf('131', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ sk_C @ X0)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ sk_C)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['129', '130'])).
% 32.11/32.33  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('133', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 32.11/32.33      inference('sup-', [status(thm)], ['25', '26'])).
% 32.11/32.33  thf('134', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ sk_C @ X0)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('demod', [status(thm)], ['131', '132', '133'])).
% 32.11/32.33  thf(fc7_funct_1, axiom,
% 32.11/32.33    (![A:$i,B:$i]:
% 32.11/32.33     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) & 
% 32.11/32.33         ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) & ( v2_funct_1 @ B ) ) =>
% 32.11/32.33       ( ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) & 
% 32.11/32.33         ( v2_funct_1 @ ( k5_relat_1 @ A @ B ) ) ) ))).
% 32.11/32.33  thf('135', plain,
% 32.11/32.33      (![X7 : $i, X8 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X7)
% 32.11/32.33          | ~ (v1_funct_1 @ X7)
% 32.11/32.33          | ~ (v1_relat_1 @ X7)
% 32.11/32.33          | ~ (v1_relat_1 @ X8)
% 32.11/32.33          | ~ (v1_funct_1 @ X8)
% 32.11/32.33          | ~ (v2_funct_1 @ X8)
% 32.11/32.33          | (v2_funct_1 @ (k5_relat_1 @ X7 @ X8)))),
% 32.11/32.33      inference('cnf', [status(esa)], [fc7_funct_1])).
% 32.11/32.33  thf('136', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v2_funct_1 @ (k5_relat_1 @ sk_C @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ sk_C)
% 32.11/32.33          | ~ (v1_funct_1 @ sk_C)
% 32.11/32.33          | ~ (v2_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup+', [status(thm)], ['134', '135'])).
% 32.11/32.33  thf('137', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('139', plain, ((v2_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('140', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v2_funct_1 @ (k5_relat_1 @ sk_C @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0)))),
% 32.11/32.33      inference('demod', [status(thm)], ['136', '137', '138', '139'])).
% 32.11/32.33  thf('141', plain,
% 32.11/32.33      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | ~ (v1_relat_1 @ 
% 32.11/32.33             (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 32.11/32.33        | ~ (v2_funct_1 @ 
% 32.11/32.33             (k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C)))
% 32.11/32.33        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['124', '140'])).
% 32.11/32.33  thf('142', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(t31_funct_2, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.11/32.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 32.11/32.33         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 32.11/32.33           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 32.11/32.33           ( m1_subset_1 @
% 32.11/32.33             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 32.11/32.33  thf('143', plain,
% 32.11/32.33      (![X48 : $i, X49 : $i, X50 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X48)
% 32.11/32.33          | ((k2_relset_1 @ X50 @ X49 @ X48) != (X49))
% 32.11/32.33          | (v1_funct_1 @ (k2_funct_1 @ X48))
% 32.11/32.33          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X49)))
% 32.11/32.33          | ~ (v1_funct_2 @ X48 @ X50 @ X49)
% 32.11/32.33          | ~ (v1_funct_1 @ X48))),
% 32.11/32.33      inference('cnf', [status(esa)], [t31_funct_2])).
% 32.11/32.33  thf('144', plain,
% 32.11/32.33      ((~ (v1_funct_1 @ sk_C)
% 32.11/32.33        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.11/32.33        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_C))),
% 32.11/32.33      inference('sup-', [status(thm)], ['142', '143'])).
% 32.11/32.33  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('146', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('147', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('148', plain, ((v2_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('149', plain,
% 32.11/32.33      (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 32.11/32.33      inference('demod', [status(thm)], ['144', '145', '146', '147', '148'])).
% 32.11/32.33  thf('150', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 32.11/32.33      inference('simplify', [status(thm)], ['149'])).
% 32.11/32.33  thf('151', plain,
% 32.11/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.11/32.33         = (k2_funct_1 @ sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['118', '121', '122', '123'])).
% 32.11/32.33  thf('152', plain,
% 32.11/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k2_funct_1 @ sk_C))
% 32.11/32.33         = (k2_funct_1 @ sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['118', '121', '122', '123'])).
% 32.11/32.33  thf('153', plain,
% 32.11/32.33      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 32.11/32.33      inference('demod', [status(thm)], ['141', '150', '151', '152'])).
% 32.11/32.33  thf('154', plain,
% 32.11/32.33      (((v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))
% 32.11/32.33        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 32.11/32.33      inference('simplify', [status(thm)], ['153'])).
% 32.11/32.33  thf('155', plain,
% 32.11/32.33      ((~ (v1_relat_1 @ sk_C)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.11/32.33        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['106', '154'])).
% 32.11/32.33  thf('156', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('158', plain,
% 32.11/32.33      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 32.11/32.33        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 32.11/32.33      inference('demod', [status(thm)], ['155', '156', '157'])).
% 32.11/32.33  thf('159', plain,
% 32.11/32.33      ((~ (v1_relat_1 @ sk_C)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.11/32.33        | ~ (v2_funct_1 @ sk_C)
% 32.11/32.33        | (v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['105', '158'])).
% 32.11/32.33  thf('160', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('161', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('163', plain, ((v2_funct_1 @ (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 32.11/32.33      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 32.11/32.33  thf('164', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf(t35_funct_2, axiom,
% 32.11/32.33    (![A:$i,B:$i,C:$i]:
% 32.11/32.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 32.11/32.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 32.11/32.33       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 32.11/32.33         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 32.11/32.33           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 32.11/32.33             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 32.11/32.33  thf('165', plain,
% 32.11/32.33      (![X51 : $i, X52 : $i, X53 : $i]:
% 32.11/32.33         (((X51) = (k1_xboole_0))
% 32.11/32.33          | ~ (v1_funct_1 @ X52)
% 32.11/32.33          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 32.11/32.33          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 32.11/32.33          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_partfun1 @ X53))
% 32.11/32.33          | ~ (v2_funct_1 @ X52)
% 32.11/32.33          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 32.11/32.33      inference('cnf', [status(esa)], [t35_funct_2])).
% 32.11/32.33  thf('166', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 32.11/32.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 32.11/32.33  thf('167', plain,
% 32.11/32.33      (![X51 : $i, X52 : $i, X53 : $i]:
% 32.11/32.33         (((X51) = (k1_xboole_0))
% 32.11/32.33          | ~ (v1_funct_1 @ X52)
% 32.11/32.33          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 32.11/32.33          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 32.11/32.33          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 32.11/32.33          | ~ (v2_funct_1 @ X52)
% 32.11/32.33          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 32.11/32.33      inference('demod', [status(thm)], ['165', '166'])).
% 32.11/32.33  thf('168', plain,
% 32.11/32.33      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_C)
% 32.11/32.33        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 32.11/32.33        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_C)
% 32.11/32.33        | ((sk_B) = (k1_xboole_0)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['164', '167'])).
% 32.11/32.33  thf('169', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('170', plain, ((v2_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('171', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('172', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('173', plain,
% 32.11/32.33      ((((sk_B) != (sk_B))
% 32.11/32.33        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 32.11/32.33        | ((sk_B) = (k1_xboole_0)))),
% 32.11/32.33      inference('demod', [status(thm)], ['168', '169', '170', '171', '172'])).
% 32.11/32.33  thf('174', plain,
% 32.11/32.33      ((((sk_B) = (k1_xboole_0))
% 32.11/32.33        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 32.11/32.33      inference('simplify', [status(thm)], ['173'])).
% 32.11/32.33  thf('175', plain, (((sk_B) != (k1_xboole_0))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('176', plain,
% 32.11/32.33      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('simplify_reflect-', [status(thm)], ['174', '175'])).
% 32.11/32.33  thf('177', plain, ((v2_funct_1 @ (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['163', '176'])).
% 32.11/32.33  thf('178', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('179', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('180', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('182', plain,
% 32.11/32.33      (((zip_tseitin_0 @ sk_D @ sk_C)
% 32.11/32.33        | (zip_tseitin_1 @ sk_A @ sk_B)
% 32.11/32.33        | ((sk_B) != (sk_B)))),
% 32.11/32.33      inference('demod', [status(thm)],
% 32.11/32.33                ['104', '177', '178', '179', '180', '181'])).
% 32.11/32.33  thf('183', plain,
% 32.11/32.33      (((zip_tseitin_1 @ sk_A @ sk_B) | (zip_tseitin_0 @ sk_D @ sk_C))),
% 32.11/32.33      inference('simplify', [status(thm)], ['182'])).
% 32.11/32.33  thf('184', plain,
% 32.11/32.33      (![X41 : $i, X42 : $i]:
% 32.11/32.33         (((X41) = (k1_xboole_0)) | ~ (zip_tseitin_1 @ X41 @ X42))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_2])).
% 32.11/32.33  thf('185', plain,
% 32.11/32.33      (((zip_tseitin_0 @ sk_D @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['183', '184'])).
% 32.11/32.33  thf('186', plain, (((sk_A) != (k1_xboole_0))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('187', plain, ((zip_tseitin_0 @ sk_D @ sk_C)),
% 32.11/32.33      inference('simplify_reflect-', [status(thm)], ['185', '186'])).
% 32.11/32.33  thf('188', plain,
% 32.11/32.33      (![X39 : $i, X40 : $i]:
% 32.11/32.33         ((v2_funct_1 @ X40) | ~ (zip_tseitin_0 @ X40 @ X39))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_4])).
% 32.11/32.33  thf('189', plain, ((v2_funct_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['187', '188'])).
% 32.11/32.33  thf('190', plain, (((sk_D) = (k2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 32.11/32.33      inference('demod', [status(thm)], ['69', '189'])).
% 32.11/32.33  thf('191', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 32.11/32.33  thf('192', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)) @ (k2_funct_1 @ X0))
% 32.11/32.33            = (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['116'])).
% 32.11/32.33  thf('193', plain,
% 32.11/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 32.11/32.33          = (k2_funct_1 @ sk_D))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_D)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_D)
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('sup+', [status(thm)], ['191', '192'])).
% 32.11/32.33  thf('194', plain, ((v1_relat_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['56', '57'])).
% 32.11/32.33  thf('195', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('196', plain,
% 32.11/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 32.11/32.33          = (k2_funct_1 @ sk_D))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['193', '194', '195'])).
% 32.11/32.33  thf('197', plain, ((v2_funct_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['187', '188'])).
% 32.11/32.33  thf('198', plain,
% 32.11/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 32.11/32.33         = (k2_funct_1 @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['196', '197'])).
% 32.11/32.33  thf('199', plain,
% 32.11/32.33      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('200', plain,
% 32.11/32.33      (![X51 : $i, X52 : $i, X53 : $i]:
% 32.11/32.33         (((X51) = (k1_xboole_0))
% 32.11/32.33          | ~ (v1_funct_1 @ X52)
% 32.11/32.33          | ~ (v1_funct_2 @ X52 @ X53 @ X51)
% 32.11/32.33          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X51)))
% 32.11/32.33          | ((k5_relat_1 @ X52 @ (k2_funct_1 @ X52)) = (k6_relat_1 @ X53))
% 32.11/32.33          | ~ (v2_funct_1 @ X52)
% 32.11/32.33          | ((k2_relset_1 @ X53 @ X51 @ X52) != (X51)))),
% 32.11/32.33      inference('demod', [status(thm)], ['165', '166'])).
% 32.11/32.33  thf('201', plain,
% 32.11/32.33      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) != (sk_A))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D)
% 32.11/32.33        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.11/32.33        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_D)
% 32.11/32.33        | ((sk_A) = (k1_xboole_0)))),
% 32.11/32.33      inference('sup-', [status(thm)], ['199', '200'])).
% 32.11/32.33  thf('202', plain,
% 32.11/32.33      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 32.11/32.33      inference('sup-', [status(thm)], ['47', '48'])).
% 32.11/32.33  thf('203', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 32.11/32.33  thf('204', plain, (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['202', '203'])).
% 32.11/32.33  thf('205', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('206', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('207', plain,
% 32.11/32.33      ((((sk_A) != (sk_A))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D)
% 32.11/32.33        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.11/32.33        | ((sk_A) = (k1_xboole_0)))),
% 32.11/32.33      inference('demod', [status(thm)], ['201', '204', '205', '206'])).
% 32.11/32.33  thf('208', plain,
% 32.11/32.33      ((((sk_A) = (k1_xboole_0))
% 32.11/32.33        | ((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('simplify', [status(thm)], ['207'])).
% 32.11/32.33  thf('209', plain, (((sk_A) != (k1_xboole_0))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('210', plain,
% 32.11/32.33      ((((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('simplify_reflect-', [status(thm)], ['208', '209'])).
% 32.11/32.33  thf('211', plain, ((v2_funct_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['187', '188'])).
% 32.11/32.33  thf('212', plain,
% 32.11/32.33      (((k5_relat_1 @ sk_D @ (k2_funct_1 @ sk_D)) = (k6_relat_1 @ sk_B))),
% 32.11/32.33      inference('demod', [status(thm)], ['210', '211'])).
% 32.11/32.33  thf('213', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['94', '95'])).
% 32.11/32.33  thf('214', plain,
% 32.11/32.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2)
% 32.11/32.33              = (k5_relat_1 @ X1 @ (k5_relat_1 @ X0 @ X2)))
% 32.11/32.33          | ~ (v1_relat_1 @ X2)
% 32.11/32.33          | ~ (v1_relat_1 @ X1))),
% 32.11/32.33      inference('cnf', [status(esa)], [t55_relat_1])).
% 32.11/32.33  thf('215', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ sk_C)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ sk_D))),
% 32.11/32.33      inference('sup+', [status(thm)], ['213', '214'])).
% 32.11/32.33  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 32.11/32.33      inference('sup-', [status(thm)], ['119', '120'])).
% 32.11/32.33  thf('217', plain, ((v1_relat_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['56', '57'])).
% 32.11/32.33  thf('218', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ X0)
% 32.11/32.33            = (k5_relat_1 @ sk_C @ (k5_relat_1 @ sk_D @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('demod', [status(thm)], ['215', '216', '217'])).
% 32.11/32.33  thf('219', plain,
% 32.11/32.33      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D))
% 32.11/32.33          = (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)))
% 32.11/32.33        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['212', '218'])).
% 32.11/32.33  thf('220', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['127', '128'])).
% 32.11/32.33  thf('221', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 32.11/32.33      inference('demod', [status(thm)], ['46', '49', '50', '51', '52'])).
% 32.11/32.33  thf('222', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('223', plain,
% 32.11/32.33      (![X6 : $i]:
% 32.11/32.33         ((v2_funct_1 @ (k2_funct_1 @ X6))
% 32.11/32.33          | ~ (v2_funct_1 @ X6)
% 32.11/32.33          | ~ (v1_funct_1 @ X6)
% 32.11/32.33          | ~ (v1_relat_1 @ X6))),
% 32.11/32.33      inference('cnf', [status(esa)], [fc6_funct_1])).
% 32.11/32.33  thf('224', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('225', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('simplify', [status(thm)], ['18'])).
% 32.11/32.33  thf('226', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('simplify', [status(thm)], ['18'])).
% 32.11/32.33  thf('227', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('228', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_funct_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('229', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ((k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 32.11/32.33              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('simplify', [status(thm)], ['18'])).
% 32.11/32.33  thf('230', plain,
% 32.11/32.33      (![X5 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ X5))
% 32.11/32.33          | ~ (v1_funct_1 @ X5)
% 32.11/32.33          | ~ (v1_relat_1 @ X5))),
% 32.11/32.33      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 32.11/32.33  thf('231', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['229', '230'])).
% 32.11/32.33  thf('232', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['228', '231'])).
% 32.11/32.33  thf('233', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['232'])).
% 32.11/32.33  thf('234', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | (v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['227', '233'])).
% 32.11/32.33  thf('235', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['234'])).
% 32.11/32.33  thf('236', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0))),
% 32.11/32.33      inference('sup+', [status(thm)], ['226', '235'])).
% 32.11/32.33  thf('237', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 32.11/32.33      inference('simplify', [status(thm)], ['236'])).
% 32.11/32.33  thf('238', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ 
% 32.11/32.33           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 32.11/32.33      inference('sup+', [status(thm)], ['225', '237'])).
% 32.11/32.33  thf('239', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | (v1_relat_1 @ 
% 32.11/32.33             (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['224', '238'])).
% 32.11/32.33  thf('240', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ 
% 32.11/32.33           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['239'])).
% 32.11/32.33  thf('241', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | (v1_relat_1 @ 
% 32.11/32.33             (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['223', '240'])).
% 32.11/32.33  thf('242', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ 
% 32.11/32.33           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 32.11/32.33          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['241'])).
% 32.11/32.33  thf('243', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         (~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | (v1_relat_1 @ 
% 32.11/32.33             (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0))))))),
% 32.11/32.33      inference('sup-', [status(thm)], ['222', '242'])).
% 32.11/32.33  thf('244', plain,
% 32.11/32.33      (![X0 : $i]:
% 32.11/32.33         ((v1_relat_1 @ 
% 32.11/32.33           (k2_funct_1 @ (k5_relat_1 @ X0 @ (k6_relat_1 @ (k2_relat_1 @ X0)))))
% 32.11/32.33          | ~ (v2_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_funct_1 @ X0)
% 32.11/32.33          | ~ (v1_relat_1 @ X0))),
% 32.11/32.33      inference('simplify', [status(thm)], ['243'])).
% 32.11/32.33  thf('245', plain,
% 32.11/32.33      (((v1_relat_1 @ (k2_funct_1 @ (k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A))))
% 32.11/32.33        | ~ (v1_relat_1 @ sk_D)
% 32.11/32.33        | ~ (v1_funct_1 @ sk_D)
% 32.11/32.33        | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('sup+', [status(thm)], ['221', '244'])).
% 32.11/32.33  thf('246', plain, (((k5_relat_1 @ sk_D @ (k6_relat_1 @ sk_A)) = (sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['55', '58'])).
% 32.11/32.33  thf('247', plain, ((v1_relat_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['56', '57'])).
% 32.11/32.33  thf('248', plain, ((v1_funct_1 @ sk_D)),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('249', plain,
% 32.11/32.33      (((v1_relat_1 @ (k2_funct_1 @ sk_D)) | ~ (v2_funct_1 @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['245', '246', '247', '248'])).
% 32.11/32.33  thf('250', plain, ((v2_funct_1 @ sk_D)),
% 32.11/32.33      inference('sup-', [status(thm)], ['187', '188'])).
% 32.11/32.33  thf('251', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_D))),
% 32.11/32.33      inference('demod', [status(thm)], ['249', '250'])).
% 32.11/32.33  thf('252', plain,
% 32.11/32.33      (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ (k2_funct_1 @ sk_D)) = (sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['219', '220', '251'])).
% 32.11/32.33  thf('253', plain, (((k2_funct_1 @ sk_D) = (sk_C))),
% 32.11/32.33      inference('sup+', [status(thm)], ['198', '252'])).
% 32.11/32.33  thf('254', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 32.11/32.33      inference('demod', [status(thm)], ['190', '253'])).
% 32.11/32.33  thf('255', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 32.11/32.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 32.11/32.33  thf('256', plain, ($false),
% 32.11/32.33      inference('simplify_reflect-', [status(thm)], ['254', '255'])).
% 32.11/32.33  
% 32.11/32.33  % SZS output end Refutation
% 32.11/32.33  
% 32.11/32.34  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
