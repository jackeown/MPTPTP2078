%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cfJbjyMY3o

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:18 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  297 (2136 expanded)
%              Number of leaves         :   44 ( 631 expanded)
%              Depth                    :   40
%              Number of atoms          : 2919 (46587 expanded)
%              Number of equality atoms :  158 (1425 expanded)
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

thf('35',plain,(
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

thf('36',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('49',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('50',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['47','52'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('54',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( v1_partfun1 @ X19 @ X20 )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','63'])).

thf('65',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X32: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X32 ) )
      | ~ ( l1_struct_0 @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['64','71'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('73',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('78',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('79',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('81',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('82',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','79','82'])).

thf('84',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['64','71'])).

thf('86',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_partfun1 @ X23 @ X22 )
      | ( ( k1_relat_1 @ X23 )
        = X22 )
      | ~ ( v4_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('90',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('92',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('98',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','98'])).

thf('100',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','99'])).

thf('101',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['42','100'])).

thf('102',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

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

thf('104',plain,(
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

thf('105',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('114',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['105','106','111','112','115'])).

thf('117',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['102','116'])).

thf('118',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('119',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['101','121'])).

thf('123',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','122'])).

thf('124',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('125',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('130',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

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

thf('135',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('140',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('144',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    ! [X31: $i] :
      ( ( ( k2_struct_0 @ X31 )
        = ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('147',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['145','150'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('156',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','137','144','156','157'])).

thf('159',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
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

thf('161',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('163',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('164',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('167',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('168',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','168'])).

thf('170',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('171',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('172',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v2_funct_1 @ X28 )
      | ( ( k2_relset_1 @ X30 @ X29 @ X28 )
       != X29 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X28 ) @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X30 @ X29 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('173',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('177',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['173','174','175','176','177'])).

thf('179',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,(
    ! [X9: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ( ( k1_relat_1 @ X9 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('181',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('183',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('184',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('186',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k5_relat_1 @ X10 @ ( k2_funct_1 @ X10 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['185','186'])).

thf('188',plain,(
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
    inference('sup-',[status(thm)],['184','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['183','189'])).

thf('191',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('192',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['190','191','192','193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['182','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,(
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

thf('201',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('203',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('204',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','98'])).

thf('206',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['169'])).

thf('207',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202','203','204','205','206'])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['181','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('210',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209','210'])).

thf('212',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['180','211'])).

thf('213',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','98'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['212','213','214','215','216'])).

thf('218',plain,(
    v2_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['217'])).

thf('219',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('220',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('221',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['161','170','179','218','221'])).

thf('223',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['127','222'])).

thf('224',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['90','91','98'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['223','224','225','226','227'])).

thf('229',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['126','229'])).

thf('231',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','230'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['77','78'])).

thf('233',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['231','232','233','234'])).

thf('236',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('237',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('238',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_funct_2 @ X24 @ X25 @ X26 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','99'])).

thf('244',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','99'])).

thf('245',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','99'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['242','243','244','245'])).

thf('247',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['236','246'])).

thf('248',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('250',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,(
    $false ),
    inference(demod,[status(thm)],['235','250'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cfJbjyMY3o
% 0.16/0.36  % Computer   : n022.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 16:13:26 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 411 iterations in 0.137s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.39/0.58  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.58  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.58  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.58  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.39/0.58  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.39/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.58  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.58  thf(t55_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ( v2_funct_1 @ A ) =>
% 0.39/0.58         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.39/0.58           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X9)
% 0.39/0.58          | ((k2_relat_1 @ X9) = (k1_relat_1 @ (k2_funct_1 @ X9)))
% 0.39/0.58          | ~ (v1_funct_1 @ X9)
% 0.39/0.58          | ~ (v1_relat_1 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.58  thf(dt_k2_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.58         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.39/0.58          | ~ (v1_funct_1 @ X4)
% 0.39/0.58          | ~ (v1_relat_1 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.39/0.58          | ~ (v1_funct_1 @ X4)
% 0.39/0.58          | ~ (v1_relat_1 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X9)
% 0.39/0.58          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.39/0.58          | ~ (v1_funct_1 @ X9)
% 0.39/0.58          | ~ (v1_relat_1 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.58  thf('4', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.39/0.58          | ~ (v1_funct_1 @ X4)
% 0.39/0.58          | ~ (v1_relat_1 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.39/0.58          | ~ (v1_funct_1 @ X4)
% 0.39/0.58          | ~ (v1_relat_1 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.58  thf(t61_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ( v2_funct_1 @ A ) =>
% 0.39/0.58         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.39/0.58             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.39/0.58           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.39/0.58             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X10 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X10)
% 0.39/0.58          | ((k5_relat_1 @ (k2_funct_1 @ X10) @ X10)
% 0.39/0.58              = (k6_relat_1 @ (k2_relat_1 @ X10)))
% 0.39/0.58          | ~ (v1_funct_1 @ X10)
% 0.39/0.58          | ~ (v1_relat_1 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.39/0.58  thf(t48_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.58           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.39/0.58               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.39/0.58             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X7)
% 0.39/0.58          | ~ (v1_funct_1 @ X7)
% 0.39/0.58          | (v2_funct_1 @ X7)
% 0.39/0.58          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.39/0.58          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.39/0.58          | ~ (v1_funct_1 @ X8)
% 0.39/0.58          | ~ (v1_relat_1 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf(fc4_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.39/0.58       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.39/0.58  thf('9', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '9'])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '11'])).
% 0.39/0.58  thf('13', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['12'])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['4', '13'])).
% 0.39/0.58  thf('15', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['14'])).
% 0.39/0.58  thf('16', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['3', '15'])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X9)
% 0.39/0.58          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.39/0.58          | ~ (v1_funct_1 @ X9)
% 0.39/0.58          | ~ (v1_relat_1 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X10 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X10)
% 0.39/0.58          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.39/0.58              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.39/0.58          | ~ (v1_funct_1 @ X10)
% 0.39/0.58          | ~ (v1_relat_1 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.39/0.58  thf(t64_funct_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.58           ( ( ( v2_funct_1 @ A ) & 
% 0.39/0.58               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.39/0.58               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.39/0.58             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (![X11 : $i, X12 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X11)
% 0.39/0.58          | ~ (v1_funct_1 @ X11)
% 0.39/0.58          | ((X11) = (k2_funct_1 @ X12))
% 0.39/0.58          | ((k5_relat_1 @ X11 @ X12) != (k6_relat_1 @ (k2_relat_1 @ X12)))
% 0.39/0.58          | ((k2_relat_1 @ X11) != (k1_relat_1 @ X12))
% 0.39/0.58          | ~ (v2_funct_1 @ X12)
% 0.39/0.58          | ~ (v1_funct_1 @ X12)
% 0.39/0.58          | ~ (v1_relat_1 @ X12))),
% 0.39/0.58      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.39/0.58            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.39/0.58              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['21'])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '24'])).
% 0.39/0.58  thf('26', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['25'])).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['2', '26'])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '28'])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.58  thf(d3_struct_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf(t64_tops_2, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( l1_struct_0 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.58           ( ![C:$i]:
% 0.39/0.58             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.58                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.58                 ( m1_subset_1 @
% 0.39/0.58                   C @ 
% 0.39/0.58                   ( k1_zfmisc_1 @
% 0.39/0.58                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.58               ( ( ( ( k2_relset_1 @
% 0.39/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.58                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.58                   ( v2_funct_1 @ C ) ) =>
% 0.39/0.58                 ( r2_funct_2 @
% 0.39/0.58                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.58                   ( k2_tops_2 @
% 0.39/0.58                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.58                     ( k2_tops_2 @
% 0.39/0.58                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.58                   C ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( l1_struct_0 @ A ) =>
% 0.39/0.58          ( ![B:$i]:
% 0.39/0.58            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.58              ( ![C:$i]:
% 0.39/0.58                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.58                    ( v1_funct_2 @
% 0.39/0.58                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.58                    ( m1_subset_1 @
% 0.39/0.58                      C @ 
% 0.39/0.58                      ( k1_zfmisc_1 @
% 0.39/0.58                        ( k2_zfmisc_1 @
% 0.39/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.58                  ( ( ( ( k2_relset_1 @
% 0.39/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.58                        ( k2_struct_0 @ B ) ) & 
% 0.39/0.58                      ( v2_funct_1 @ C ) ) =>
% 0.39/0.58                    ( r2_funct_2 @
% 0.39/0.58                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.58                      ( k2_tops_2 @
% 0.39/0.58                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.58                        ( k2_tops_2 @
% 0.39/0.58                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.58                      C ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.58           sk_C)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['37', '38'])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.58           sk_C)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['34', '39'])).
% 0.39/0.58  thf('41', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (((m1_subset_1 @ sk_C @ 
% 0.39/0.58         (k1_zfmisc_1 @ 
% 0.39/0.58          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['43', '44'])).
% 0.39/0.58  thf('46', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('53', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.58      inference('demod', [status(thm)], ['47', '52'])).
% 0.39/0.58  thf(cc5_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.39/0.58             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.39/0.58          | (v1_partfun1 @ X19 @ X20)
% 0.39/0.58          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.39/0.58          | ~ (v1_funct_1 @ X19)
% 0.39/0.58          | (v1_xboole_0 @ X21))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.58  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('57', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['57', '58'])).
% 0.39/0.58  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('61', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.58  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('63', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['61', '62'])).
% 0.39/0.58  thf('64', plain,
% 0.39/0.58      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['55', '56', '63'])).
% 0.39/0.58  thf('65', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf(fc5_struct_0, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.58       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.39/0.58  thf('66', plain,
% 0.39/0.58      (![X32 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ (k2_struct_0 @ X32))
% 0.39/0.58          | ~ (l1_struct_0 @ X32)
% 0.39/0.58          | (v2_struct_0 @ X32))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.39/0.58  thf('67', plain,
% 0.39/0.58      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | (v2_struct_0 @ sk_B)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.58  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('69', plain,
% 0.39/0.58      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['67', '68'])).
% 0.39/0.58  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('71', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('clc', [status(thm)], ['69', '70'])).
% 0.39/0.58  thf('72', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['64', '71'])).
% 0.39/0.58  thf(d4_partfun1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.58       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.39/0.58  thf('73', plain,
% 0.39/0.58      (![X22 : $i, X23 : $i]:
% 0.39/0.58         (~ (v1_partfun1 @ X23 @ X22)
% 0.39/0.58          | ((k1_relat_1 @ X23) = (X22))
% 0.39/0.58          | ~ (v4_relat_1 @ X23 @ X22)
% 0.39/0.58          | ~ (v1_relat_1 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.58  thf('74', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.39/0.58        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['72', '73'])).
% 0.39/0.58  thf('75', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(cc2_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.58  thf('76', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.39/0.58          | (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.58  thf('77', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ 
% 0.39/0.58           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.39/0.58        | (v1_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.58  thf(fc6_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.58  thf('78', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.58  thf('79', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('80', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(cc2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.58  thf('81', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         ((v4_relat_1 @ X13 @ X14)
% 0.39/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.58  thf('82', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['80', '81'])).
% 0.39/0.58  thf('83', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['74', '79', '82'])).
% 0.39/0.58  thf('84', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('85', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('clc', [status(thm)], ['64', '71'])).
% 0.39/0.58  thf('86', plain,
% 0.39/0.58      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['84', '85'])).
% 0.39/0.58  thf('87', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('88', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['86', '87'])).
% 0.39/0.58  thf('89', plain,
% 0.39/0.58      (![X22 : $i, X23 : $i]:
% 0.39/0.58         (~ (v1_partfun1 @ X23 @ X22)
% 0.39/0.58          | ((k1_relat_1 @ X23) = (X22))
% 0.39/0.58          | ~ (v4_relat_1 @ X23 @ X22)
% 0.39/0.58          | ~ (v1_relat_1 @ X23))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.58  thf('90', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.39/0.58        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['88', '89'])).
% 0.39/0.58  thf('91', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('92', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('93', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('94', plain,
% 0.39/0.58      (((m1_subset_1 @ sk_C @ 
% 0.39/0.58         (k1_zfmisc_1 @ 
% 0.39/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['92', '93'])).
% 0.39/0.58  thf('95', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('96', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('97', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         ((v4_relat_1 @ X13 @ X14)
% 0.39/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.58  thf('98', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['96', '97'])).
% 0.39/0.58  thf('99', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['90', '91', '98'])).
% 0.39/0.58  thf('100', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['83', '99'])).
% 0.39/0.58  thf('101', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['42', '100'])).
% 0.39/0.58  thf('102', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('103', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf(d4_tops_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.39/0.58         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.39/0.58  thf('104', plain,
% 0.39/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.39/0.58          | ~ (v2_funct_1 @ X35)
% 0.39/0.58          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.39/0.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.39/0.58          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.39/0.58          | ~ (v1_funct_1 @ X35))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.58  thf('105', plain,
% 0.39/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.58        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58            = (k2_funct_1 @ sk_C))
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.58        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58            != (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['103', '104'])).
% 0.39/0.58  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('107', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('108', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('109', plain,
% 0.39/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['107', '108'])).
% 0.39/0.58  thf('110', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('111', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['109', '110'])).
% 0.39/0.58  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('113', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('114', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.58  thf('115', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['113', '114'])).
% 0.39/0.58  thf('116', plain,
% 0.39/0.58      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58          = (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('demod', [status(thm)], ['105', '106', '111', '112', '115'])).
% 0.39/0.58  thf('117', plain,
% 0.39/0.58      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.58        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58            = (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['102', '116'])).
% 0.39/0.58  thf('118', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('119', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('120', plain,
% 0.39/0.58      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.39/0.58        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58            = (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.39/0.58  thf('121', plain,
% 0.39/0.58      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_funct_1 @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['120'])).
% 0.39/0.58  thf('122', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58           (k2_funct_1 @ sk_C)) @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['101', '121'])).
% 0.39/0.58  thf('123', plain,
% 0.39/0.58      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_funct_1 @ sk_C)) @ 
% 0.39/0.58           sk_C)
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['33', '122'])).
% 0.39/0.58  thf('124', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('125', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('126', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58           (k2_funct_1 @ sk_C)) @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.39/0.58  thf('127', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X9)
% 0.39/0.58          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.39/0.58          | ~ (v1_funct_1 @ X9)
% 0.39/0.58          | ~ (v1_relat_1 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.58  thf('128', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('129', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('130', plain,
% 0.39/0.58      (((m1_subset_1 @ sk_C @ 
% 0.39/0.58         (k1_zfmisc_1 @ 
% 0.39/0.58          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['128', '129'])).
% 0.39/0.58  thf('131', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('132', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['130', '131'])).
% 0.39/0.58  thf('133', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('134', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.58      inference('demod', [status(thm)], ['132', '133'])).
% 0.39/0.58  thf(t31_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.39/0.58         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.39/0.58           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.39/0.58           ( m1_subset_1 @
% 0.39/0.58             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('135', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X28)
% 0.39/0.58          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.39/0.58          | (m1_subset_1 @ (k2_funct_1 @ X28) @ 
% 0.39/0.58             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.39/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.39/0.58          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.39/0.58          | ~ (v1_funct_1 @ X28))),
% 0.39/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.58  thf('136', plain,
% 0.39/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.58           (k1_zfmisc_1 @ 
% 0.39/0.58            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.39/0.58        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.58            != (k2_relat_1 @ sk_C))
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['134', '135'])).
% 0.39/0.58  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('138', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('139', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['109', '110'])).
% 0.39/0.58  thf('140', plain,
% 0.39/0.58      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['138', '139'])).
% 0.39/0.58  thf('141', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('142', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['140', '141'])).
% 0.39/0.58  thf('143', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('144', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['142', '143'])).
% 0.39/0.58  thf('145', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('146', plain,
% 0.39/0.58      (![X31 : $i]:
% 0.39/0.58         (((k2_struct_0 @ X31) = (u1_struct_0 @ X31)) | ~ (l1_struct_0 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.58  thf('147', plain,
% 0.39/0.58      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('148', plain,
% 0.39/0.58      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58          = (k2_struct_0 @ sk_B))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.58      inference('sup+', [status(thm)], ['146', '147'])).
% 0.39/0.58  thf('149', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('150', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['148', '149'])).
% 0.39/0.58  thf('151', plain,
% 0.39/0.58      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58          = (k2_struct_0 @ sk_B))
% 0.39/0.58        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['145', '150'])).
% 0.39/0.58  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('153', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.58         = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['151', '152'])).
% 0.39/0.58  thf('154', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('155', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('156', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.58         = (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.39/0.58  thf('157', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('158', plain,
% 0.39/0.58      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.58         (k1_zfmisc_1 @ 
% 0.39/0.58          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))
% 0.39/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['136', '137', '144', '156', '157'])).
% 0.39/0.58  thf('159', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['158'])).
% 0.39/0.58  thf('160', plain,
% 0.39/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X34 @ X33 @ X35) != (X33))
% 0.39/0.58          | ~ (v2_funct_1 @ X35)
% 0.39/0.58          | ((k2_tops_2 @ X34 @ X33 @ X35) = (k2_funct_1 @ X35))
% 0.39/0.58          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.39/0.58          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.39/0.58          | ~ (v1_funct_1 @ X35))),
% 0.39/0.58      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.58  thf('161', plain,
% 0.39/0.58      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.58             (k2_struct_0 @ sk_A))
% 0.39/0.58        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['159', '160'])).
% 0.39/0.58  thf('162', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.58      inference('demod', [status(thm)], ['132', '133'])).
% 0.39/0.58  thf('163', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X28)
% 0.39/0.58          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.39/0.58          | (v1_funct_1 @ (k2_funct_1 @ X28))
% 0.39/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.39/0.58          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.39/0.58          | ~ (v1_funct_1 @ X28))),
% 0.39/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.58  thf('164', plain,
% 0.39/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.58            != (k2_relat_1 @ sk_C))
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['162', '163'])).
% 0.39/0.58  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('166', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['142', '143'])).
% 0.39/0.58  thf('167', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.58         = (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.39/0.58  thf('168', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('169', plain,
% 0.39/0.58      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['164', '165', '166', '167', '168'])).
% 0.39/0.58  thf('170', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['169'])).
% 0.39/0.58  thf('171', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.58      inference('demod', [status(thm)], ['132', '133'])).
% 0.39/0.58  thf('172', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X28)
% 0.39/0.58          | ((k2_relset_1 @ X30 @ X29 @ X28) != (X29))
% 0.39/0.58          | (v1_funct_2 @ (k2_funct_1 @ X28) @ X29 @ X30)
% 0.39/0.58          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29)))
% 0.39/0.58          | ~ (v1_funct_2 @ X28 @ X30 @ X29)
% 0.39/0.58          | ~ (v1_funct_1 @ X28))),
% 0.39/0.58      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.58  thf('173', plain,
% 0.39/0.58      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.39/0.58        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.58           (k2_struct_0 @ sk_A))
% 0.39/0.58        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.58            != (k2_relat_1 @ sk_C))
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['171', '172'])).
% 0.39/0.58  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('175', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['142', '143'])).
% 0.39/0.58  thf('176', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.58         = (k2_relat_1 @ sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.39/0.58  thf('177', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('178', plain,
% 0.39/0.58      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.58         (k2_struct_0 @ sk_A))
% 0.39/0.58        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['173', '174', '175', '176', '177'])).
% 0.39/0.58  thf('179', plain,
% 0.39/0.58      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.58        (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('simplify', [status(thm)], ['178'])).
% 0.39/0.58  thf('180', plain,
% 0.39/0.58      (![X9 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X9)
% 0.39/0.58          | ((k1_relat_1 @ X9) = (k2_relat_1 @ (k2_funct_1 @ X9)))
% 0.39/0.58          | ~ (v1_funct_1 @ X9)
% 0.39/0.58          | ~ (v1_relat_1 @ X9))),
% 0.39/0.58      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.58  thf('181', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.39/0.58          | ~ (v1_funct_1 @ X4)
% 0.39/0.58          | ~ (v1_relat_1 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.58  thf('182', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['16'])).
% 0.39/0.58  thf('183', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['169'])).
% 0.39/0.58  thf('184', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.39/0.58          | ~ (v1_funct_1 @ X4)
% 0.39/0.58          | ~ (v1_relat_1 @ X4))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.39/0.58  thf('185', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.58  thf('186', plain,
% 0.39/0.58      (![X10 : $i]:
% 0.39/0.58         (~ (v2_funct_1 @ X10)
% 0.39/0.58          | ((k5_relat_1 @ X10 @ (k2_funct_1 @ X10))
% 0.39/0.58              = (k6_relat_1 @ (k1_relat_1 @ X10)))
% 0.39/0.58          | ~ (v1_funct_1 @ X10)
% 0.39/0.58          | ~ (v1_relat_1 @ X10))),
% 0.39/0.58      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.39/0.58  thf('187', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.39/0.58            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.58      inference('sup+', [status(thm)], ['185', '186'])).
% 0.39/0.58  thf('188', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.39/0.58              = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['184', '187'])).
% 0.39/0.58  thf('189', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k5_relat_1 @ (k2_funct_1 @ X0) @ X0)
% 0.39/0.58            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.39/0.58          | ~ (v2_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['188'])).
% 0.39/0.58  thf('190', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.58        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.39/0.58            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['183', '189'])).
% 0.39/0.58  thf('191', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('192', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('193', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('194', plain,
% 0.39/0.58      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.39/0.58            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.58      inference('demod', [status(thm)], ['190', '191', '192', '193'])).
% 0.39/0.58  thf('195', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.58        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.39/0.58            = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['182', '194'])).
% 0.39/0.58  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('198', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('199', plain,
% 0.39/0.58      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 0.39/0.58         = (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.58      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 0.39/0.58  thf('200', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X7)
% 0.39/0.58          | ~ (v1_funct_1 @ X7)
% 0.39/0.58          | (v2_funct_1 @ X7)
% 0.39/0.58          | ((k2_relat_1 @ X7) != (k1_relat_1 @ X8))
% 0.39/0.58          | ~ (v2_funct_1 @ (k5_relat_1 @ X7 @ X8))
% 0.39/0.58          | ~ (v1_funct_1 @ X8)
% 0.39/0.58          | ~ (v1_relat_1 @ X8))),
% 0.39/0.58      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.39/0.58  thf('201', plain,
% 0.39/0.58      ((~ (v2_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C))))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))
% 0.39/0.58        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['199', '200'])).
% 0.39/0.58  thf('202', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.39/0.58  thf('203', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('204', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('205', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['90', '91', '98'])).
% 0.39/0.58  thf('206', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['169'])).
% 0.39/0.58  thf('207', plain,
% 0.39/0.58      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.39/0.58        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)],
% 0.39/0.58                ['201', '202', '203', '204', '205', '206'])).
% 0.39/0.58  thf('208', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['181', '207'])).
% 0.39/0.58  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('210', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('211', plain,
% 0.39/0.58      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['208', '209', '210'])).
% 0.39/0.58  thf('212', plain,
% 0.39/0.58      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.58        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['180', '211'])).
% 0.39/0.58  thf('213', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['90', '91', '98'])).
% 0.39/0.58  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('217', plain,
% 0.39/0.58      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.39/0.58        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('demod', [status(thm)], ['212', '213', '214', '215', '216'])).
% 0.39/0.58  thf('218', plain, ((v2_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.58      inference('simplify', [status(thm)], ['217'])).
% 0.39/0.58  thf('219', plain,
% 0.39/0.58      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['158'])).
% 0.39/0.58  thf('220', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.39/0.58          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.58  thf('221', plain,
% 0.39/0.58      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['219', '220'])).
% 0.39/0.58  thf('222', plain,
% 0.39/0.58      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.58        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.39/0.58      inference('demod', [status(thm)], ['161', '170', '179', '218', '221'])).
% 0.39/0.58  thf('223', plain,
% 0.39/0.58      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.58        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['127', '222'])).
% 0.39/0.58  thf('224', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['90', '91', '98'])).
% 0.39/0.58  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('228', plain,
% 0.39/0.58      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.39/0.58        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.58      inference('demod', [status(thm)], ['223', '224', '225', '226', '227'])).
% 0.39/0.58  thf('229', plain,
% 0.39/0.58      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.39/0.58         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['228'])).
% 0.39/0.58  thf('230', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.58          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['126', '229'])).
% 0.39/0.58  thf('231', plain,
% 0.39/0.58      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.58           sk_C)
% 0.39/0.58        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['32', '230'])).
% 0.39/0.58  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['77', '78'])).
% 0.39/0.58  thf('233', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('234', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('235', plain,
% 0.39/0.58      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.58          sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['231', '232', '233', '234'])).
% 0.39/0.58  thf('236', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('demod', [status(thm)], ['94', '95'])).
% 0.39/0.58  thf('237', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_C @ 
% 0.39/0.58        (k1_zfmisc_1 @ 
% 0.39/0.58         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(reflexivity_r2_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.58         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.58       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.39/0.58  thf('238', plain,
% 0.39/0.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.58         ((r2_funct_2 @ X24 @ X25 @ X26 @ X26)
% 0.39/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.39/0.58          | ~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.39/0.58          | ~ (v1_funct_1 @ X26)
% 0.39/0.58          | ~ (v1_funct_1 @ X27)
% 0.39/0.58          | ~ (v1_funct_2 @ X27 @ X24 @ X25)
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.39/0.58      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.39/0.58  thf('239', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.58             (k1_zfmisc_1 @ 
% 0.39/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.58          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.58             sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['237', '238'])).
% 0.39/0.58  thf('240', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('241', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('242', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.58             (k1_zfmisc_1 @ 
% 0.39/0.58              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.58          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.58             sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['239', '240', '241'])).
% 0.39/0.58  thf('243', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['83', '99'])).
% 0.39/0.58  thf('244', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['83', '99'])).
% 0.39/0.58  thf('245', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.39/0.58      inference('demod', [status(thm)], ['83', '99'])).
% 0.39/0.58  thf('246', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ 
% 0.39/0.58             (k1_zfmisc_1 @ 
% 0.39/0.58              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.58          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.58          | ~ (v1_funct_1 @ X0)
% 0.39/0.58          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.58             sk_C))),
% 0.39/0.58      inference('demod', [status(thm)], ['242', '243', '244', '245'])).
% 0.39/0.58  thf('247', plain,
% 0.39/0.58      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.39/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.58        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['236', '246'])).
% 0.39/0.58  thf('248', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('249', plain,
% 0.39/0.58      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['109', '110'])).
% 0.39/0.58  thf('250', plain,
% 0.39/0.58      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.39/0.58      inference('demod', [status(thm)], ['247', '248', '249'])).
% 0.39/0.58  thf('251', plain, ($false), inference('demod', [status(thm)], ['235', '250'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.39/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
