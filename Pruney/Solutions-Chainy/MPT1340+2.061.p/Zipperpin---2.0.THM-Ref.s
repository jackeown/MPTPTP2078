%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y3toARD4ub

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:16 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  251 (1215 expanded)
%              Number of leaves         :   44 ( 373 expanded)
%              Depth                    :   40
%              Number of atoms          : 2583 (25710 expanded)
%              Number of equality atoms :  138 ( 780 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

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

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('4',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('6',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X10 ) @ X10 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
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
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('19',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k2_funct_1 @ X12 ) )
      | ( ( k5_relat_1 @ X11 @ X12 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
      | ( ( k2_relat_1 @ X11 )
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v2_funct_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('35',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','54','57'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('59',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('60',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('66',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('71',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('72',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','69'])).

thf('73',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','70','71','72'])).

thf('74',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('83',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('84',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('87',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['86','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['96','101'])).

thf('103',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['84','85','94','95','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['73','106'])).

thf('108',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

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

thf('110',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('111',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('114',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('115',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115'])).

thf('117',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X33 @ X35 )
       != X33 )
      | ~ ( v2_funct_1 @ X35 )
      | ( ( k2_tops_2 @ X34 @ X33 @ X35 )
        = ( k2_funct_1 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('121',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('130',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('131',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('134',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('135',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('139',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('141',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('142',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('144',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('150',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['148','149','150','151'])).

thf('153',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['140','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('155',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['153','154','155','156'])).

thf('158',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ( v2_funct_1 @ X7 )
      | ( ( k2_relat_1 @ X7 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('159',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('161',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('162',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('164',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['127'])).

thf('165',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163','164'])).

thf('166',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','165'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['138','169'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('172',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('173',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174'])).

thf('176',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('178',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('179',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','128','137','176','179'])).

thf('181',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['108','180'])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('183',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('184',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['181','182','183','184','185'])).

thf('187',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['107','187'])).

thf('189',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','188'])).

thf('190',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['52','53'])).

thf('191',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['189','190','191','192'])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('196',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198','199'])).

thf('201',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','200'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('204',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['201','202','203'])).

thf('205',plain,(
    $false ),
    inference(demod,[status(thm)],['193','204'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y3toARD4ub
% 0.15/0.34  % Computer   : n022.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 18:27:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 497 iterations in 0.194s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.66  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.66  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.66  thf(t55_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) =>
% 0.45/0.66         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.66           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X9 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X9)
% 0.45/0.66          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf(dt_k2_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.66         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X4 : $i]:
% 0.45/0.66         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X4)
% 0.45/0.66          | ~ (v1_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X4 : $i]:
% 0.45/0.66         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X4)
% 0.45/0.66          | ~ (v1_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X9 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X9)
% 0.45/0.66          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X4 : $i]:
% 0.45/0.66         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X4)
% 0.45/0.66          | ~ (v1_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X4 : $i]:
% 0.45/0.66         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X4)
% 0.45/0.66          | ~ (v1_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.66  thf(t61_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) =>
% 0.45/0.66         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.45/0.66             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.45/0.66           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.45/0.66             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X10 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X10)
% 0.45/0.66          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.45/0.66              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.45/0.66          | ~ (v1_funct_1 @ X10)
% 0.45/0.66          | ~ (v1_relat_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.66  thf(t48_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.45/0.66               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.45/0.66             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7)
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | (v2_funct_1 @ X7)
% 0.45/0.66          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.45/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (v1_relat_1 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf(fc4_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.45/0.66       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.45/0.66  thf('9', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['5', '11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '13'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '15'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X9 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X9)
% 0.45/0.66          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X10 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X10)
% 0.45/0.66          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.45/0.66              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.45/0.66          | ~ (v1_funct_1 @ X10)
% 0.45/0.66          | ~ (v1_relat_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.66  thf(t64_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66           ( ( ( v2_funct_1 @ A ) & 
% 0.45/0.66               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.45/0.66               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.45/0.66             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X11 : $i, X12 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X11)
% 0.45/0.66          | ~ (v1_funct_1 @ X11)
% 0.45/0.66          | ((X11) = (k2_funct_1 @ X12))
% 0.45/0.66          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 0.45/0.66          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 0.45/0.66          | ~ (v2_funct_1 @ X12)
% 0.45/0.66          | ~ (v1_funct_1 @ X12)
% 0.45/0.66          | ~ (v1_relat_1 @ X12))),
% 0.45/0.66      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.45/0.66            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.45/0.66              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['18', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['17', '24'])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['27'])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['29'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '30'])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.66  thf(d3_struct_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf(t64_tops_2, conjecture,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_struct_0 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.66           ( ![C:$i]:
% 0.45/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.66                 ( m1_subset_1 @
% 0.45/0.66                   C @ 
% 0.45/0.66                   ( k1_zfmisc_1 @
% 0.45/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.66               ( ( ( ( k2_relset_1 @
% 0.45/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.45/0.66                   ( v2_funct_1 @ C ) ) =>
% 0.45/0.66                 ( r2_funct_2 @
% 0.45/0.66                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.66                   ( k2_tops_2 @
% 0.45/0.66                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.66                     ( k2_tops_2 @
% 0.45/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.66                   C ) ) ) ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]:
% 0.45/0.66        ( ( l1_struct_0 @ A ) =>
% 0.45/0.66          ( ![B:$i]:
% 0.45/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.45/0.66              ( ![C:$i]:
% 0.45/0.66                ( ( ( v1_funct_1 @ C ) & 
% 0.45/0.66                    ( v1_funct_2 @
% 0.45/0.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.45/0.66                    ( m1_subset_1 @
% 0.45/0.66                      C @ 
% 0.45/0.66                      ( k1_zfmisc_1 @
% 0.45/0.66                        ( k2_zfmisc_1 @
% 0.45/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.45/0.66                  ( ( ( ( k2_relset_1 @
% 0.45/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.45/0.66                        ( k2_struct_0 @ B ) ) & 
% 0.45/0.66                      ( v2_funct_1 @ C ) ) =>
% 0.45/0.66                    ( r2_funct_2 @
% 0.45/0.66                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.45/0.66                      ( k2_tops_2 @
% 0.45/0.66                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.45/0.66                        ( k2_tops_2 @
% 0.45/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.45/0.66                      C ) ) ) ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66           sk_C)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['34', '35'])).
% 0.45/0.66  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66           sk_C)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '38'])).
% 0.45/0.66  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['39', '40'])).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc5_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.45/0.66       ( ![C:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.45/0.66             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.45/0.66          | (v1_partfun1 @ X19 @ X20)
% 0.45/0.66          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.45/0.66          | ~ (v1_funct_1 @ X19)
% 0.45/0.66          | (v1_xboole_0 @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.66  thf('45', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.66  thf(d4_partfun1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.66  thf('48', plain,
% 0.45/0.66      (![X22 : $i, X23 : $i]:
% 0.45/0.66         (~ (v1_partfun1 @ X23 @ X22)
% 0.45/0.66          | ((k1_relat_1 @ X23) = (X22))
% 0.45/0.66          | ~ (v4_relat_1 @ X23 @ X22)
% 0.45/0.66          | ~ (v1_relat_1 @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc2_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.66          | (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.66  thf('52', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ 
% 0.45/0.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.66        | (v1_relat_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['50', '51'])).
% 0.45/0.66  thf(fc6_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.66  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.66         ((v4_relat_1 @ X13 @ X14)
% 0.45/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.66  thf('57', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['49', '54', '57'])).
% 0.45/0.66  thf(fc2_struct_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.66       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X32 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X32))
% 0.45/0.66          | ~ (l1_struct_0 @ X32)
% 0.45/0.66          | (v2_struct_0 @ X32))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | (v2_struct_0 @ sk_B)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.66  thf('61', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['60', '61'])).
% 0.45/0.66  thf('63', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('64', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['62', '63'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('66', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['62', '63'])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('69', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.66  thf('70', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['64', '69'])).
% 0.45/0.66  thf('71', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['64', '69'])).
% 0.45/0.66  thf('72', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['64', '69'])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '70', '71', '72'])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('75', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_C @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['75', '76'])).
% 0.45/0.66  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('79', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_C @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['74', '79'])).
% 0.45/0.66  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf(d4_tops_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.66         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.45/0.66          | ~ (v2_funct_1 @ X35)
% 0.45/0.66          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.45/0.66          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.45/0.66          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.45/0.66          | ~ (v1_funct_1 @ X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            = (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['82', '83'])).
% 0.45/0.66  thf('85', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['87', '88'])).
% 0.45/0.66  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['86', '91'])).
% 0.45/0.66  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('96', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      (![X31 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('98', plain,
% 0.45/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('99', plain,
% 0.45/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66          = (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['97', '98'])).
% 0.45/0.66  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('101', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['99', '100'])).
% 0.45/0.66  thf('102', plain,
% 0.45/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66          = (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['96', '101'])).
% 0.45/0.66  thf('103', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('104', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('105', plain,
% 0.45/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66          = (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85', '94', '95', '104'])).
% 0.45/0.66  thf('106', plain,
% 0.45/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['105'])).
% 0.45/0.66  thf('107', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['73', '106'])).
% 0.45/0.66  thf('108', plain,
% 0.45/0.66      (![X9 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X9)
% 0.45/0.66          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf('109', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf(t31_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.66         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.66           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.66           ( m1_subset_1 @
% 0.45/0.66             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('110', plain,
% 0.45/0.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X28)
% 0.45/0.66          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.45/0.66          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.45/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.45/0.66          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.45/0.66          | ~ (v1_funct_1 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.66  thf('111', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66           (k1_zfmisc_1 @ 
% 0.45/0.66            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['109', '110'])).
% 0.45/0.66  thf('112', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('113', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('114', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('115', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('116', plain,
% 0.45/0.66      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['111', '112', '113', '114', '115'])).
% 0.45/0.66  thf('117', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['116'])).
% 0.45/0.66  thf('118', plain,
% 0.45/0.66      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.45/0.66          | ~ (v2_funct_1 @ X35)
% 0.45/0.66          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.45/0.66          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.45/0.66          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.45/0.66          | ~ (v1_funct_1 @ X35))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.66  thf('119', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66             (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['117', '118'])).
% 0.45/0.66  thf('120', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('121', plain,
% 0.45/0.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X28)
% 0.45/0.66          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.45/0.66          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.45/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.45/0.66          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.45/0.66          | ~ (v1_funct_1 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.66  thf('122', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['120', '121'])).
% 0.45/0.66  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('124', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('125', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('127', plain,
% 0.45/0.66      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.45/0.66  thf('128', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['127'])).
% 0.45/0.66  thf('129', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['80', '81'])).
% 0.45/0.66  thf('130', plain,
% 0.45/0.66      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X28)
% 0.45/0.66          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.45/0.66          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.45/0.66          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.45/0.66          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.45/0.66          | ~ (v1_funct_1 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.66  thf('131', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66           (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['129', '130'])).
% 0.45/0.66  thf('132', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('133', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('134', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('135', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('136', plain,
% 0.45/0.66      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66         (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['131', '132', '133', '134', '135'])).
% 0.45/0.66  thf('137', plain,
% 0.45/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66        (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('simplify', [status(thm)], ['136'])).
% 0.45/0.66  thf('138', plain,
% 0.45/0.66      (![X9 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X9)
% 0.45/0.66          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf('139', plain,
% 0.45/0.66      (![X4 : $i]:
% 0.45/0.66         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X4)
% 0.45/0.66          | ~ (v1_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.66  thf('140', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['16'])).
% 0.45/0.66  thf('141', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['127'])).
% 0.45/0.66  thf('142', plain,
% 0.45/0.66      (![X4 : $i]:
% 0.45/0.66         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.45/0.66          | ~ (v1_funct_1 @ X4)
% 0.45/0.66          | ~ (v1_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.45/0.66  thf('143', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['31'])).
% 0.45/0.66  thf('144', plain,
% 0.45/0.66      (![X10 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X10)
% 0.45/0.66          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.45/0.66              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.45/0.66          | ~ (v1_funct_1 @ X10)
% 0.45/0.66          | ~ (v1_relat_1 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.66  thf('145', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.45/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['143', '144'])).
% 0.45/0.66  thf('146', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.45/0.66              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['142', '145'])).
% 0.45/0.66  thf('147', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.45/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['146'])).
% 0.45/0.66  thf('148', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['141', '147'])).
% 0.45/0.66  thf('149', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('150', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('151', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('152', plain,
% 0.45/0.66      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.66      inference('demod', [status(thm)], ['148', '149', '150', '151'])).
% 0.45/0.66  thf('153', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.66            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['140', '152'])).
% 0.45/0.66  thf('154', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('155', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('157', plain,
% 0.45/0.66      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.45/0.66         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('demod', [status(thm)], ['153', '154', '155', '156'])).
% 0.45/0.66  thf('158', plain,
% 0.45/0.66      (![X7 : $i, X8 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X7)
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | (v2_funct_1 @ X7)
% 0.45/0.66          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.45/0.66          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ~ (v1_relat_1 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.45/0.66  thf('159', plain,
% 0.45/0.66      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.45/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['157', '158'])).
% 0.45/0.66  thf('160', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.45/0.66  thf('161', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('162', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('163', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.66  thf('164', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['127'])).
% 0.45/0.66  thf('165', plain,
% 0.45/0.66      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('demod', [status(thm)],
% 0.45/0.66                ['159', '160', '161', '162', '163', '164'])).
% 0.45/0.66  thf('166', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['139', '165'])).
% 0.45/0.66  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('169', plain,
% 0.45/0.66      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.45/0.66  thf('170', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['138', '169'])).
% 0.45/0.66  thf('171', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.66  thf('172', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('173', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('174', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('175', plain,
% 0.45/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('demod', [status(thm)], ['170', '171', '172', '173', '174'])).
% 0.45/0.66  thf('176', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['175'])).
% 0.45/0.66  thf('177', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['116'])).
% 0.45/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('178', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.45/0.66          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.66  thf('179', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['177', '178'])).
% 0.45/0.66  thf('180', plain,
% 0.45/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['119', '128', '137', '176', '179'])).
% 0.45/0.66  thf('181', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['108', '180'])).
% 0.45/0.66  thf('182', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.66  thf('183', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('184', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('185', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('186', plain,
% 0.45/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('demod', [status(thm)], ['181', '182', '183', '184', '185'])).
% 0.45/0.66  thf('187', plain,
% 0.45/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['186'])).
% 0.45/0.66  thf('188', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['107', '187'])).
% 0.45/0.66  thf('189', plain,
% 0.45/0.66      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66           sk_C)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['32', '188'])).
% 0.45/0.66  thf('190', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['52', '53'])).
% 0.45/0.66  thf('191', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('192', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('193', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['189', '190', '191', '192'])).
% 0.45/0.66  thf('194', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.66  thf('195', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.66  thf(reflexivity_r2_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.66         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.45/0.66  thf('196', plain,
% 0.45/0.66      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.45/0.66          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.45/0.66          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.45/0.66          | ~ (v1_funct_1 @ X26)
% 0.45/0.66          | ~ (v1_funct_1 @ X27)
% 0.45/0.66          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.45/0.66          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.45/0.66      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.45/0.66  thf('197', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.66             (k1_zfmisc_1 @ 
% 0.45/0.66              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66          | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66             sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['195', '196'])).
% 0.45/0.66  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('199', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.66  thf('200', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.66             (k1_zfmisc_1 @ 
% 0.45/0.66              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66             sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['197', '198', '199'])).
% 0.45/0.67  thf('201', plain,
% 0.45/0.67      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.45/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.67        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.67      inference('sup-', [status(thm)], ['194', '200'])).
% 0.45/0.67  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('203', plain,
% 0.45/0.67      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['89', '90'])).
% 0.45/0.67  thf('204', plain,
% 0.45/0.67      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.67      inference('demod', [status(thm)], ['201', '202', '203'])).
% 0.45/0.67  thf('205', plain, ($false), inference('demod', [status(thm)], ['193', '204'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
