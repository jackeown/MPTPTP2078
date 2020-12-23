%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MH5wEecrD7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:17 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  329 (2175 expanded)
%              Number of leaves         :   44 ( 661 expanded)
%              Depth                    :   43
%              Number of atoms          : 3151 (42645 expanded)
%              Number of equality atoms :  140 (1095 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('4',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf('5',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( v1_funct_1 @ X12 )
      | ( X12
        = ( k2_funct_1 @ X13 ) )
      | ( ( k5_relat_1 @ X12 @ X13 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X13 ) ) )
      | ( ( k2_relat_1 @ X12 )
       != ( k1_relat_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('7',plain,(
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
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
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
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
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
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
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
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
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
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
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
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
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

thf('21',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X34: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('46',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('52',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('53',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('58',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('59',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','56','57','58'])).

thf('60',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X33: $i] :
      ( ( ( k2_struct_0 @ X33 )
        = ( u1_struct_0 @ X33 ) )
      | ~ ( l1_struct_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('84',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','80','81','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['59','92'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('95',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('96',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('97',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('98',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('99',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('100',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('102',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('103',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('104',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('110',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != X23 )
      | ( v1_partfun1 @ X24 @ X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('113',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v4_relat_1 @ X24 @ ( k1_relat_1 @ X24 ) )
      | ( v1_partfun1 @ X24 @ ( k1_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['101','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130','131'])).

thf('133',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('134',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('136',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('137',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('138',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('139',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('140',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('141',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('142',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['141','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['140','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['139','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','151'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['135','155'])).

thf('157',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('158',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','160'])).

thf('162',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','161'])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','162'])).

thf('164',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['163','164','165'])).

thf('167',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k2_relat_1 @ X10 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('172',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

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

thf('174',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v2_funct_1 @ X29 )
      | ( ( k2_relset_1 @ X31 @ X30 @ X29 )
       != X30 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('175',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('178',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['175','176','177','178','179'])).

thf('181',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['172','181'])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('185',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','186'])).

thf('188',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('189',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('192',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('193',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('196',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('197',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('201',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['201','202','203','204'])).

thf('206',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_partfun1 @ X24 @ X23 )
      | ( ( k1_relat_1 @ X24 )
        = X23 )
      | ~ ( v4_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('207',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('210',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['208','209'])).

thf('211',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('212',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['210','211','212','213'])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['207','214'])).

thf('216',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','215'])).

thf('217',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('218',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['180'])).

thf('221',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['193','219','220'])).

thf('222',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['95','221'])).

thf('223',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('224',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('225',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['222','223','224'])).

thf('226',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k2_relset_1 @ X36 @ X35 @ X37 )
       != X35 )
      | ~ ( v2_funct_1 @ X37 )
      | ( ( k2_tops_2 @ X36 @ X35 @ X37 )
        = ( k2_funct_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('227',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['225','226'])).

thf('228',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['180'])).

thf('229',plain,(
    ! [X10: $i] :
      ( ~ ( v2_funct_1 @ X10 )
      | ( ( k1_relat_1 @ X10 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X10 ) ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('230',plain,(
    ! [X4: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('231',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('232',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('233',plain,(
    ! [X32: $i] :
      ( ( v1_funct_2 @ X32 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('234',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['231','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('237',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['235','236','237'])).

thf('239',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['230','238'])).

thf('240',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('241',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['239','240','241'])).

thf('243',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['229','242'])).

thf('244',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('245',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('246',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['243','244','245','246','247'])).

thf('249',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('250',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('251',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ ( k2_relat_1 @ X32 ) ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('252',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['250','253'])).

thf('255',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['180'])).

thf('256',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['249','256'])).

thf('258',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('259',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['257','258','259'])).

thf('261',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('262',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['187','188','189','190'])).

thf('263',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['227','228','248','263'])).

thf('265',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','265'])).

thf('267',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('268',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['266','267','268','269'])).

thf('271',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['93','270'])).

thf('272',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','271'])).

thf('273',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('274',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( r2_funct_2 @ X26 @ X27 @ X25 @ X28 )
      | ( X25 != X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('275',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(simplify,[status(thm)],['274'])).

thf('276',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['273','275'])).

thf('277',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('278',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['276','277','278'])).

thf('280',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('281',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('282',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,(
    $false ),
    inference(demod,[status(thm)],['272','279','280','281','282'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MH5wEecrD7
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:21 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 417 iterations in 0.179s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.64  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.64  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.64  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.64  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.64  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.64  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.64  thf(t55_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_1 @ A ) =>
% 0.46/0.64         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.64           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('0', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf(dt_k2_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf(fc6_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.64         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.64         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.46/0.64          | ~ (v2_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_relat_1 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf(t61_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v2_funct_1 @ A ) =>
% 0.46/0.64         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.64             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.64           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.64             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X11 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X11)
% 0.46/0.64          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 0.46/0.64              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.46/0.64          | ~ (v1_funct_1 @ X11)
% 0.46/0.64          | ~ (v1_relat_1 @ X11))),
% 0.46/0.64      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.64  thf(t64_funct_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.64           ( ( ( v2_funct_1 @ A ) & 
% 0.46/0.64               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.46/0.64               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.46/0.64             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X12 : $i, X13 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X12)
% 0.46/0.64          | ~ (v1_funct_1 @ X12)
% 0.46/0.64          | ((X12) = (k2_funct_1 @ X13))
% 0.46/0.64          | ((k5_relat_1 @ X12 @ X13) != (k6_relat_1 @ (k2_relat_1 @ X13)))
% 0.46/0.64          | ((k2_relat_1 @ X12) != (k1_relat_1 @ X13))
% 0.46/0.64          | ~ (v2_funct_1 @ X13)
% 0.46/0.64          | ~ (v1_funct_1 @ X13)
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.46/0.64  thf('7', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.46/0.64            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.46/0.64              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['4', '8'])).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '10'])).
% 0.46/0.64  thf('12', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.64  thf('13', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['2', '12'])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '14'])).
% 0.46/0.64  thf('16', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.64  thf('17', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['0', '16'])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.64  thf(d3_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('20', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf(t64_tops_2, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( l1_struct_0 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                 ( m1_subset_1 @
% 0.46/0.64                   C @ 
% 0.46/0.64                   ( k1_zfmisc_1 @
% 0.46/0.64                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64               ( ( ( ( k2_relset_1 @
% 0.46/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.64                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.64                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.64                 ( r2_funct_2 @
% 0.46/0.64                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.64                   ( k2_tops_2 @
% 0.46/0.64                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.64                     ( k2_tops_2 @
% 0.46/0.64                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.64                   C ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( l1_struct_0 @ A ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64                    ( v1_funct_2 @
% 0.46/0.64                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.64                    ( m1_subset_1 @
% 0.46/0.64                      C @ 
% 0.46/0.64                      ( k1_zfmisc_1 @
% 0.46/0.64                        ( k2_zfmisc_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.64                  ( ( ( ( k2_relset_1 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.64                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.64                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.64                    ( r2_funct_2 @
% 0.46/0.64                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.64                      ( k2_tops_2 @
% 0.46/0.64                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.64                        ( k2_tops_2 @
% 0.46/0.64                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.64                      C ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('22', plain,
% 0.46/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64           sk_C)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.64  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64           sk_C)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['19', '24'])).
% 0.46/0.64  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('27', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.64  thf('28', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc5_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.64       ( ![C:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.64             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.64          | (v1_partfun1 @ X20 @ X21)
% 0.46/0.64          | ~ (v1_funct_2 @ X20 @ X21 @ X22)
% 0.46/0.64          | ~ (v1_funct_1 @ X20)
% 0.46/0.64          | (v1_xboole_0 @ X22))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.64  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('32', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.46/0.64  thf(d4_partfun1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.64       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X24 @ X23)
% 0.46/0.64          | ((k1_relat_1 @ X24) = (X23))
% 0.46/0.64          | ~ (v4_relat_1 @ X24 @ X23)
% 0.46/0.64          | ~ (v1_relat_1 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('35', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relat_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ A ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.64  thf('37', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ 
% 0.46/0.64           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.64        | (v1_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.64  thf(fc6_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.64  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.64  thf('42', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X14 @ X15)
% 0.46/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('43', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['35', '40', '43'])).
% 0.46/0.64  thf(fc2_struct_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.64       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X34 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ (u1_struct_0 @ X34))
% 0.46/0.64          | ~ (l1_struct_0 @ X34)
% 0.46/0.64          | (v2_struct_0 @ X34))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.64  thf('46', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.46/0.64        | (v2_struct_0 @ sk_B)
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.64  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.64  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('52', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['51', '52'])).
% 0.46/0.64  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('55', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('56', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.64  thf('57', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.64  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.64  thf('59', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['27', '56', '57', '58'])).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('62', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.64  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('65', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf('66', plain,
% 0.46/0.64      (((m1_subset_1 @ sk_C @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['60', '65'])).
% 0.46/0.64  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('68', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf(d4_tops_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.64         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.46/0.64          | ~ (v2_funct_1 @ X37)
% 0.46/0.64          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.46/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.46/0.64          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.46/0.64          | ~ (v1_funct_1 @ X37))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.64  thf('70', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64            = (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64            != (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('74', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('77', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['72', '77'])).
% 0.46/0.64  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.64  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      (![X33 : $i]:
% 0.46/0.64         (((k2_struct_0 @ X33) = (u1_struct_0 @ X33)) | ~ (l1_struct_0 @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.64  thf('84', plain,
% 0.46/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('85', plain,
% 0.46/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64          = (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.64      inference('sup+', [status(thm)], ['83', '84'])).
% 0.46/0.64  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64          = (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['82', '87'])).
% 0.46/0.64  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64          = (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('demod', [status(thm)], ['70', '71', '80', '81', '90'])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['91'])).
% 0.46/0.64  thf('93', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64          sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['59', '92'])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.46/0.64          | ~ (v2_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_relat_1 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('95', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.46/0.64          | ~ (v2_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_relat_1 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('101', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.46/0.64          | ~ (v2_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_relat_1 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('106', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('108', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf(t3_funct_2, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.64       ( ( v1_funct_1 @ A ) & 
% 0.46/0.64         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           A @ 
% 0.46/0.64           ( k1_zfmisc_1 @
% 0.46/0.64             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      (![X32 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X32 @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.46/0.64          | ~ (v1_funct_1 @ X32)
% 0.46/0.64          | ~ (v1_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.64         ((v4_relat_1 @ X14 @ X15)
% 0.46/0.64          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]:
% 0.46/0.64         (((k1_relat_1 @ X24) != (X23))
% 0.46/0.64          | (v1_partfun1 @ X24 @ X23)
% 0.46/0.64          | ~ (v4_relat_1 @ X24 @ X23)
% 0.46/0.64          | ~ (v1_relat_1 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('113', plain,
% 0.46/0.64      (![X24 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X24)
% 0.46/0.64          | ~ (v4_relat_1 @ X24 @ (k1_relat_1 @ X24))
% 0.46/0.64          | (v1_partfun1 @ X24 @ (k1_relat_1 @ X24)))),
% 0.46/0.64      inference('simplify', [status(thm)], ['112'])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['111', '113'])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['114'])).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['108', '115'])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['107', '116'])).
% 0.46/0.64  thf('118', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['117'])).
% 0.46/0.64  thf('119', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['106', '118'])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.64  thf('121', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['105', '120'])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['104', '121'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['122'])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['103', '123'])).
% 0.46/0.64  thf('125', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['124'])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['102', '125'])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64         (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['101', '127'])).
% 0.46/0.64  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('131', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('132', plain,
% 0.46/0.64      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['128', '129', '130', '131'])).
% 0.46/0.64  thf('133', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X24 @ X23)
% 0.46/0.64          | ((k1_relat_1 @ X24) = (X23))
% 0.46/0.64          | ~ (v4_relat_1 @ X24 @ X23)
% 0.46/0.64          | ~ (v1_relat_1 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('134', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64             (k2_struct_0 @ sk_A))
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64            = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['132', '133'])).
% 0.46/0.64  thf('135', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      (![X5 : $i]:
% 0.46/0.64         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.46/0.64          | ~ (v2_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_funct_1 @ X5)
% 0.46/0.64          | ~ (v1_relat_1 @ X5))),
% 0.46/0.64      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.64  thf('137', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('138', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('139', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('140', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('141', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('142', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('143', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.64  thf('144', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['142', '143'])).
% 0.46/0.64  thf('145', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['141', '144'])).
% 0.46/0.64  thf('146', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['145'])).
% 0.46/0.64  thf('147', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['140', '146'])).
% 0.46/0.64  thf('148', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.64  thf('149', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['139', '148'])).
% 0.46/0.64  thf('150', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['138', '149'])).
% 0.46/0.64  thf('151', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['150'])).
% 0.46/0.64  thf('152', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['137', '151'])).
% 0.46/0.64  thf('153', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['152'])).
% 0.46/0.64  thf('154', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['136', '153'])).
% 0.46/0.64  thf('155', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['154'])).
% 0.46/0.64  thf('156', plain,
% 0.46/0.64      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['135', '155'])).
% 0.46/0.64  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('160', plain,
% 0.46/0.64      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.46/0.64  thf('161', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64            = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['134', '160'])).
% 0.46/0.64  thf('162', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64            = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['100', '161'])).
% 0.46/0.64  thf('163', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64            = (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['99', '162'])).
% 0.46/0.64  thf('164', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('166', plain,
% 0.46/0.64      ((((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64          = (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['163', '164', '165'])).
% 0.46/0.64  thf('167', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64            = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['98', '166'])).
% 0.46/0.64  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('170', plain,
% 0.46/0.64      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64         = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['167', '168', '169'])).
% 0.46/0.64  thf('171', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k2_relat_1 @ X10) = (k1_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('172', plain,
% 0.46/0.64      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['170', '171'])).
% 0.46/0.64  thf('173', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf(t31_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.64         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.64           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.64           ( m1_subset_1 @
% 0.46/0.64             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.64  thf('174', plain,
% 0.46/0.64      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X29)
% 0.46/0.64          | ((k2_relset_1 @ X31 @ X30 @ X29) != (X30))
% 0.46/0.64          | (v1_funct_1 @ (k2_funct_1 @ X29))
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.46/0.64          | ~ (v1_funct_2 @ X29 @ X31 @ X30)
% 0.46/0.64          | ~ (v1_funct_1 @ X29))),
% 0.46/0.64      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.64  thf('175', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64            != (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['173', '174'])).
% 0.46/0.64  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('177', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.64  thf('178', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.64  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('180', plain,
% 0.46/0.64      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('demod', [status(thm)], ['175', '176', '177', '178', '179'])).
% 0.46/0.64  thf('181', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['180'])).
% 0.46/0.64  thf('182', plain,
% 0.46/0.64      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['172', '181'])).
% 0.46/0.64  thf('183', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['97', '182'])).
% 0.46/0.64  thf('184', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('185', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('186', plain,
% 0.46/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.46/0.64  thf('187', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['96', '186'])).
% 0.46/0.64  thf('188', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('189', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('190', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('191', plain,
% 0.46/0.64      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.46/0.64  thf('192', plain,
% 0.46/0.64      (![X32 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X32 @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.46/0.64          | ~ (v1_funct_1 @ X32)
% 0.46/0.64          | ~ (v1_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.64  thf('193', plain,
% 0.46/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.64           (k2_struct_0 @ sk_A))))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['191', '192'])).
% 0.46/0.64  thf('194', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('195', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.64  thf('196', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.46/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.64  thf('197', plain,
% 0.46/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_relat_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['195', '196'])).
% 0.46/0.64  thf('198', plain,
% 0.46/0.64      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.64         = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('199', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['197', '198'])).
% 0.46/0.64  thf('200', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.64  thf('201', plain,
% 0.46/0.64      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['199', '200'])).
% 0.46/0.64  thf('202', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('205', plain,
% 0.46/0.64      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['201', '202', '203', '204'])).
% 0.46/0.64  thf('206', plain,
% 0.46/0.64      (![X23 : $i, X24 : $i]:
% 0.46/0.64         (~ (v1_partfun1 @ X24 @ X23)
% 0.46/0.64          | ((k1_relat_1 @ X24) = (X23))
% 0.46/0.64          | ~ (v4_relat_1 @ X24 @ X23)
% 0.46/0.64          | ~ (v1_relat_1 @ X24))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.64  thf('207', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['205', '206'])).
% 0.46/0.64  thf('208', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('sup+', [status(thm)], ['197', '198'])).
% 0.46/0.64  thf('209', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.64          | ~ (v2_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X0))),
% 0.46/0.64      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.64  thf('210', plain,
% 0.46/0.64      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['208', '209'])).
% 0.46/0.64  thf('211', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('212', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('213', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('214', plain,
% 0.46/0.64      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['210', '211', '212', '213'])).
% 0.46/0.64  thf('215', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('demod', [status(thm)], ['207', '214'])).
% 0.46/0.64  thf('216', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['194', '215'])).
% 0.46/0.64  thf('217', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('218', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('219', plain,
% 0.46/0.64      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.46/0.64  thf('220', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['180'])).
% 0.46/0.64  thf('221', plain,
% 0.46/0.64      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['193', '219', '220'])).
% 0.46/0.64  thf('222', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['95', '221'])).
% 0.46/0.64  thf('223', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('224', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('225', plain,
% 0.46/0.64      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.64      inference('demod', [status(thm)], ['222', '223', '224'])).
% 0.46/0.64  thf('226', plain,
% 0.46/0.64      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X36 @ X35 @ X37) != (X35))
% 0.46/0.64          | ~ (v2_funct_1 @ X37)
% 0.46/0.64          | ((k2_tops_2 @ X36 @ X35 @ X37) = (k2_funct_1 @ X37))
% 0.46/0.64          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.46/0.64          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.46/0.64          | ~ (v1_funct_1 @ X37))),
% 0.46/0.64      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.64  thf('227', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64             (k2_struct_0 @ sk_A))
% 0.46/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['225', '226'])).
% 0.46/0.64  thf('228', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['180'])).
% 0.46/0.64  thf('229', plain,
% 0.46/0.64      (![X10 : $i]:
% 0.46/0.64         (~ (v2_funct_1 @ X10)
% 0.46/0.64          | ((k1_relat_1 @ X10) = (k2_relat_1 @ (k2_funct_1 @ X10)))
% 0.46/0.64          | ~ (v1_funct_1 @ X10)
% 0.46/0.64          | ~ (v1_relat_1 @ X10))),
% 0.46/0.64      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.64  thf('230', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('231', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('232', plain,
% 0.46/0.64      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.46/0.64  thf('233', plain,
% 0.46/0.64      (![X32 : $i]:
% 0.46/0.64         ((v1_funct_2 @ X32 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))
% 0.46/0.64          | ~ (v1_funct_1 @ X32)
% 0.46/0.64          | ~ (v1_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.64  thf('234', plain,
% 0.46/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['232', '233'])).
% 0.46/0.64  thf('235', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['231', '234'])).
% 0.46/0.64  thf('236', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('237', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('238', plain,
% 0.46/0.64      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('demod', [status(thm)], ['235', '236', '237'])).
% 0.46/0.64  thf('239', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['230', '238'])).
% 0.46/0.64  thf('240', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('241', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('242', plain,
% 0.46/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['239', '240', '241'])).
% 0.46/0.64  thf('243', plain,
% 0.46/0.64      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64         (k1_relat_1 @ sk_C))
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup+', [status(thm)], ['229', '242'])).
% 0.46/0.64  thf('244', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.64  thf('245', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('246', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('247', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('248', plain,
% 0.46/0.64      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64        (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['243', '244', '245', '246', '247'])).
% 0.46/0.64  thf('249', plain,
% 0.46/0.64      (![X4 : $i]:
% 0.46/0.64         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.46/0.64          | ~ (v1_funct_1 @ X4)
% 0.46/0.64          | ~ (v1_relat_1 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.64  thf('250', plain,
% 0.46/0.64      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.46/0.64  thf('251', plain,
% 0.46/0.64      (![X32 : $i]:
% 0.46/0.64         ((m1_subset_1 @ X32 @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ (k2_relat_1 @ X32))))
% 0.46/0.64          | ~ (v1_funct_1 @ X32)
% 0.46/0.64          | ~ (v1_relat_1 @ X32))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.46/0.64  thf('252', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.46/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.64  thf('253', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.46/0.64              = (k2_relat_1 @ X0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['251', '252'])).
% 0.46/0.64  thf('254', plain,
% 0.46/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.64          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('sup+', [status(thm)], ['250', '253'])).
% 0.46/0.64  thf('255', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.64      inference('simplify', [status(thm)], ['180'])).
% 0.46/0.64  thf('256', plain,
% 0.46/0.64      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.64          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['254', '255'])).
% 0.46/0.64  thf('257', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64            (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.64            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['249', '256'])).
% 0.46/0.64  thf('258', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('259', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('260', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.64         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.64         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['257', '258', '259'])).
% 0.46/0.64  thf('261', plain,
% 0.46/0.64      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.46/0.64  thf('262', plain,
% 0.46/0.64      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['187', '188', '189', '190'])).
% 0.46/0.64  thf('263', plain,
% 0.46/0.64      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)], ['260', '261', '262'])).
% 0.46/0.64  thf('264', plain,
% 0.46/0.64      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.64        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.64      inference('demod', [status(thm)], ['227', '228', '248', '263'])).
% 0.46/0.64  thf('265', plain,
% 0.46/0.64      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['264'])).
% 0.46/0.64  thf('266', plain,
% 0.46/0.64      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.64        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['94', '265'])).
% 0.46/0.64  thf('267', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('268', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('269', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('270', plain,
% 0.46/0.64      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.64         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.64      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 0.46/0.64  thf('271', plain,
% 0.46/0.64      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.64          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['93', '270'])).
% 0.46/0.64  thf('272', plain,
% 0.46/0.64      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           sk_C)
% 0.46/0.64        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['18', '271'])).
% 0.46/0.64  thf('273', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_C @ 
% 0.46/0.64        (k1_zfmisc_1 @ 
% 0.46/0.64         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.64  thf(redefinition_r2_funct_2, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.64         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.64  thf('274', plain,
% 0.46/0.64      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.64          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.46/0.64          | ~ (v1_funct_1 @ X25)
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.46/0.64          | (r2_funct_2 @ X26 @ X27 @ X25 @ X28)
% 0.46/0.64          | ((X25) != (X28)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.46/0.64  thf('275', plain,
% 0.46/0.64      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.46/0.64         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['274'])).
% 0.46/0.64  thf('276', plain,
% 0.46/0.64      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.64        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.64           sk_C))),
% 0.46/0.64      inference('sup-', [status(thm)], ['273', '275'])).
% 0.46/0.64  thf('277', plain,
% 0.46/0.64      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.64      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.64  thf('278', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('279', plain,
% 0.46/0.64      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['276', '277', '278'])).
% 0.46/0.64  thf('280', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.64      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.64  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('282', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('283', plain, ($false),
% 0.46/0.64      inference('demod', [status(thm)], ['272', '279', '280', '281', '282'])).
% 0.46/0.64  
% 0.46/0.64  % SZS output end Refutation
% 0.46/0.64  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
