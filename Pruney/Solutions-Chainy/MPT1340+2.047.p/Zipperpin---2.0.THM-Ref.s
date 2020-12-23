%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tarVEkyAx6

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:14 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  331 (1791 expanded)
%              Number of leaves         :   46 ( 545 expanded)
%              Depth                    :   41
%              Number of atoms          : 3196 (35278 expanded)
%              Number of equality atoms :  144 ( 943 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('4',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X14: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k5_relat_1 @ X14 @ ( k2_funct_1 @ X14 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X15
        = ( k2_funct_1 @ X16 ) )
      | ( ( k5_relat_1 @ X15 @ X16 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X16 ) ) )
      | ( ( k2_relat_1 @ X15 )
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v2_funct_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
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
    ! [X38: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X38 ) )
      | ~ ( l1_struct_0 @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    ! [X37: $i] :
      ( ( ( k2_struct_0 @ X37 )
        = ( u1_struct_0 @ X37 ) )
      | ~ ( l1_struct_0 @ X37 ) ) ),
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
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('95',plain,(
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

thf('96',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('97',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('101',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['97','98','99','100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X39 @ X41 )
       != X39 )
      | ~ ( v2_funct_1 @ X41 )
      | ( ( k2_tops_2 @ X40 @ X39 @ X41 )
        = ( k2_funct_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X39 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('107',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('108',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('111',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('112',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('116',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('117',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('120',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('124',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('125',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('127',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['126'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X35 ) @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('129',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v4_relat_1 @ X17 @ X18 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != X26 )
      | ( v1_partfun1 @ X27 @ X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('133',plain,(
    ! [X27: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ~ ( v4_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) )
      | ( v1_partfun1 @ X27 @ ( k1_relat_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['125','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['123','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['122','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('143',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['141','142','143','144'])).

thf('146',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('147',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('149',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('150',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('151',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['150','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['149','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['148','157'])).

thf('159',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['158','159','160','161'])).

thf('163',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['147','162'])).

thf('164',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','163'])).

thf('165',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('166',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['126'])).

thf('169',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( v1_funct_2 @ X35 @ ( k1_relat_1 @ X35 ) @ X36 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['167','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('173',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['116','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('176',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['115','177'])).

thf('179',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['178','179','180','181','182'])).

thf('184',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('185',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('187',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('191',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['184','191'])).

thf('193',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('194',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('197',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('198',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('199',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('200',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('201',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('202',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('203',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('204',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('205',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['208'])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['203','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['202','211'])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['212'])).

thf('214',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['201','213'])).

thf('215',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('216',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['214','215','216','217'])).

thf('219',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['218','219'])).

thf('221',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('222',plain,(
    ! [X8: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('223',plain,(
    ! [X7: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('224',plain,(
    ! [X7: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('225',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k1_relat_1 @ X13 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['225','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['224','227'])).

thf('229',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['228'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['223','229'])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['230'])).

thf('232',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['222','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['221','233'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('236',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('237',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('238',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['234','235','236','237'])).

thf('239',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['220','238'])).

thf('240',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['200','239'])).

thf('241',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['199','240'])).

thf('242',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('243',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['241','242','243'])).

thf('245',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['198','244'])).

thf('246',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('247',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['245','246','247'])).

thf('249',plain,(
    ! [X13: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('250',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['248','249'])).

thf('251',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['113'])).

thf('252',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['250','251'])).

thf('253',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['197','252'])).

thf('254',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('255',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['253','254','255'])).

thf('257',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['196','256'])).

thf('258',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('259',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['257','258','259','260'])).

thf('262',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['257','258','259','260'])).

thf('263',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['195','261','262'])).

thf('264',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','114','183','263'])).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_funct_2 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('275',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_funct_2 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tarVEkyAx6
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:11:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.66  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.66  % Solved by: fo/fo7.sh
% 0.46/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.66  % done 473 iterations in 0.191s
% 0.46/0.66  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.66  % SZS output start Refutation
% 0.46/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.66  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.46/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.66  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.46/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.46/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.46/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.66  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.46/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.46/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.46/0.66  thf(t55_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v2_funct_1 @ A ) =>
% 0.46/0.66         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.46/0.66           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('0', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf(dt_k2_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.66         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.66  thf('1', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('2', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf(fc6_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.66         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.46/0.66         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.46/0.66  thf('3', plain,
% 0.46/0.66      (![X8 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.46/0.66          | ~ (v2_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_relat_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('4', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf(t61_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ( v2_funct_1 @ A ) =>
% 0.46/0.66         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.46/0.66             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.46/0.66           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.46/0.66             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('5', plain,
% 0.46/0.66      (![X14 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X14)
% 0.46/0.66          | ((k5_relat_1 @ X14 @ (k2_funct_1 @ X14))
% 0.46/0.66              = (k6_relat_1 @ (k1_relat_1 @ X14)))
% 0.46/0.66          | ~ (v1_funct_1 @ X14)
% 0.46/0.66          | ~ (v1_relat_1 @ X14))),
% 0.46/0.66      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.46/0.66  thf(t64_funct_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66           ( ( ( v2_funct_1 @ A ) & 
% 0.46/0.66               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.46/0.66               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.46/0.66             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('6', plain,
% 0.46/0.66      (![X15 : $i, X16 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X15)
% 0.46/0.66          | ~ (v1_funct_1 @ X15)
% 0.46/0.66          | ((X15) = (k2_funct_1 @ X16))
% 0.46/0.66          | ((k5_relat_1 @ X15 @ X16) != (k6_relat_1 @ (k2_relat_1 @ X16)))
% 0.46/0.66          | ((k2_relat_1 @ X15) != (k1_relat_1 @ X16))
% 0.46/0.66          | ~ (v2_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_funct_1 @ X16)
% 0.46/0.66          | ~ (v1_relat_1 @ X16))),
% 0.46/0.66      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.46/0.66  thf('7', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.46/0.66            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.66  thf('8', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.46/0.66              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.66  thf('9', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['4', '8'])).
% 0.46/0.66  thf('10', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.46/0.66  thf('11', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['3', '10'])).
% 0.46/0.66  thf('12', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.46/0.66  thf('13', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['2', '12'])).
% 0.46/0.66  thf('14', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['13'])).
% 0.46/0.66  thf('15', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['1', '14'])).
% 0.46/0.66  thf('16', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['15'])).
% 0.46/0.66  thf('17', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['0', '16'])).
% 0.46/0.66  thf('18', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.66  thf(d3_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.46/0.66  thf('19', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('20', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf(t64_tops_2, conjecture,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( l1_struct_0 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.66           ( ![C:$i]:
% 0.46/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                 ( m1_subset_1 @
% 0.46/0.66                   C @ 
% 0.46/0.66                   ( k1_zfmisc_1 @
% 0.46/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66               ( ( ( ( k2_relset_1 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                   ( v2_funct_1 @ C ) ) =>
% 0.46/0.66                 ( r2_funct_2 @
% 0.46/0.66                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.66                   ( k2_tops_2 @
% 0.46/0.66                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                     ( k2_tops_2 @
% 0.46/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.66                   C ) ) ) ) ) ) ))).
% 0.46/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.66    (~( ![A:$i]:
% 0.46/0.66        ( ( l1_struct_0 @ A ) =>
% 0.46/0.66          ( ![B:$i]:
% 0.46/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.46/0.66              ( ![C:$i]:
% 0.46/0.66                ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.66                    ( v1_funct_2 @
% 0.46/0.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.46/0.66                    ( m1_subset_1 @
% 0.46/0.66                      C @ 
% 0.46/0.66                      ( k1_zfmisc_1 @
% 0.46/0.66                        ( k2_zfmisc_1 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.46/0.66                  ( ( ( ( k2_relset_1 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.46/0.66                        ( k2_struct_0 @ B ) ) & 
% 0.46/0.66                      ( v2_funct_1 @ C ) ) =>
% 0.46/0.66                    ( r2_funct_2 @
% 0.46/0.66                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.46/0.66                      ( k2_tops_2 @
% 0.46/0.66                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.46/0.66                        ( k2_tops_2 @
% 0.46/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.46/0.66                      C ) ) ) ) ) ) ) )),
% 0.46/0.66    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.46/0.66  thf('21', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('22', plain,
% 0.46/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66           sk_C)
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.66  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('24', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.46/0.66  thf('25', plain,
% 0.46/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66           sk_C)
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['19', '24'])).
% 0.46/0.66  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('27', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['25', '26'])).
% 0.46/0.66  thf('28', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc5_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.66       ( ![C:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.46/0.66             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('29', plain,
% 0.46/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.46/0.66          | (v1_partfun1 @ X23 @ X24)
% 0.46/0.66          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.46/0.66          | ~ (v1_funct_1 @ X23)
% 0.46/0.66          | (v1_xboole_0 @ X25))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.46/0.66  thf('30', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.66  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('32', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('33', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.46/0.66  thf(d4_partfun1, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.46/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.46/0.66  thf('34', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i]:
% 0.46/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.46/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.66  thf('35', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.46/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.46/0.66  thf('36', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relat_1, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( v1_relat_1 @ A ) =>
% 0.46/0.66       ( ![B:$i]:
% 0.46/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.46/0.66  thf('37', plain,
% 0.46/0.66      (![X3 : $i, X4 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.46/0.66          | (v1_relat_1 @ X3)
% 0.46/0.66          | ~ (v1_relat_1 @ X4))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.46/0.66  thf('38', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ 
% 0.46/0.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.46/0.66        | (v1_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.46/0.66  thf(fc6_relat_1, axiom,
% 0.46/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.46/0.66  thf('39', plain,
% 0.46/0.66      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.46/0.66  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('41', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(cc2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.66  thf('42', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('43', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.66  thf('44', plain,
% 0.46/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['35', '40', '43'])).
% 0.46/0.66  thf(fc2_struct_0, axiom,
% 0.46/0.66    (![A:$i]:
% 0.46/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.46/0.66       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.46/0.66  thf('45', plain,
% 0.46/0.66      (![X38 : $i]:
% 0.46/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X38))
% 0.46/0.66          | ~ (l1_struct_0 @ X38)
% 0.46/0.66          | (v2_struct_0 @ X38))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.46/0.66  thf('46', plain,
% 0.46/0.66      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.46/0.66        | (v2_struct_0 @ sk_B)
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup-', [status(thm)], ['44', '45'])).
% 0.46/0.66  thf('47', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('48', plain,
% 0.46/0.66      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.66  thf('49', plain, (~ (v2_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.66  thf('51', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('52', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.66  thf('53', plain,
% 0.46/0.66      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['51', '52'])).
% 0.46/0.66  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('55', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('56', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.66  thf('57', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.66  thf('58', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['50', '55'])).
% 0.46/0.66  thf('59', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['27', '56', '57', '58'])).
% 0.46/0.66  thf('60', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('61', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('62', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('63', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_C @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['61', '62'])).
% 0.46/0.66  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('65', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.66  thf('66', plain,
% 0.46/0.66      (((m1_subset_1 @ sk_C @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['60', '65'])).
% 0.46/0.66  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('68', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf(d4_tops_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.46/0.66         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.46/0.66  thf('69', plain,
% 0.46/0.66      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 0.46/0.66          | ~ (v2_funct_1 @ X41)
% 0.46/0.66          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 0.46/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.46/0.66          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.46/0.66          | ~ (v1_funct_1 @ X41))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.66  thf('70', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.66  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('72', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('73', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('74', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('75', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['73', '74'])).
% 0.46/0.66  thf('76', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('77', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.66  thf('78', plain,
% 0.46/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['72', '77'])).
% 0.46/0.66  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('80', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.66  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('82', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('83', plain,
% 0.46/0.66      (![X37 : $i]:
% 0.46/0.66         (((k2_struct_0 @ X37) = (u1_struct_0 @ X37)) | ~ (l1_struct_0 @ X37))),
% 0.46/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.46/0.66  thf('84', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('85', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.46/0.66      inference('sup+', [status(thm)], ['83', '84'])).
% 0.46/0.66  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('87', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['85', '86'])).
% 0.46/0.66  thf('88', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['82', '87'])).
% 0.46/0.66  thf('89', plain, ((l1_struct_0 @ sk_B)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('90', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.66  thf('91', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66          = (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['70', '71', '80', '81', '90'])).
% 0.46/0.66  thf('92', plain,
% 0.46/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['91'])).
% 0.46/0.66  thf('93', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66           (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66          sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['59', '92'])).
% 0.46/0.66  thf('94', plain,
% 0.46/0.66      (![X8 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.46/0.66          | ~ (v2_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_relat_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('95', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf(t31_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.46/0.66         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.46/0.66           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.46/0.66           ( m1_subset_1 @
% 0.46/0.66             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('96', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X32)
% 0.46/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.46/0.66          | (m1_subset_1 @ (k2_funct_1 @ X32) @ 
% 0.46/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.46/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.46/0.66          | ~ (v1_funct_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.66  thf('97', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66           (k1_zfmisc_1 @ 
% 0.46/0.66            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.66  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('99', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.66  thf('100', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.66  thf('101', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('102', plain,
% 0.46/0.66      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66         (k1_zfmisc_1 @ 
% 0.46/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['97', '98', '99', '100', '101'])).
% 0.46/0.66  thf('103', plain,
% 0.46/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['102'])).
% 0.46/0.66  thf('104', plain,
% 0.46/0.66      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X40 @ X39 @ X41) != (X39))
% 0.46/0.66          | ~ (v2_funct_1 @ X41)
% 0.46/0.66          | ((k2_tops_2 @ X40 @ X39 @ X41) = (k2_funct_1 @ X41))
% 0.46/0.66          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 0.46/0.66          | ~ (v1_funct_2 @ X41 @ X40 @ X39)
% 0.46/0.66          | ~ (v1_funct_1 @ X41))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.46/0.66  thf('105', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66             (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['103', '104'])).
% 0.46/0.66  thf('106', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['66', '67'])).
% 0.46/0.66  thf('107', plain,
% 0.46/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X32)
% 0.46/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.46/0.66          | (v1_funct_1 @ (k2_funct_1 @ X32))
% 0.46/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.46/0.66          | ~ (v1_funct_1 @ X32))),
% 0.46/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.46/0.66  thf('108', plain,
% 0.46/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66            != (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['106', '107'])).
% 0.46/0.66  thf('109', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('110', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.46/0.66  thf('111', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['88', '89'])).
% 0.46/0.66  thf('112', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('113', plain,
% 0.46/0.66      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.46/0.66  thf('114', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['113'])).
% 0.46/0.66  thf('115', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf('116', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('117', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('118', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i]:
% 0.46/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.66  thf('119', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('120', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_relat_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['118', '119'])).
% 0.46/0.66  thf('121', plain,
% 0.46/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.46/0.66         = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('122', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['120', '121'])).
% 0.46/0.66  thf('123', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('124', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('125', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf(d10_xboole_0, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.66  thf('126', plain,
% 0.46/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.46/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.66  thf('127', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.66      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.66  thf(t4_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i]:
% 0.46/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.66       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.66         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.46/0.66           ( m1_subset_1 @
% 0.46/0.66             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.46/0.66  thf('128', plain,
% 0.46/0.66      (![X35 : $i, X36 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 0.46/0.66          | (m1_subset_1 @ X35 @ 
% 0.46/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X35) @ X36)))
% 0.46/0.66          | ~ (v1_funct_1 @ X35)
% 0.46/0.66          | ~ (v1_relat_1 @ X35))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.46/0.66  thf('129', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (m1_subset_1 @ X0 @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.66  thf('130', plain,
% 0.46/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.66         ((v4_relat_1 @ X17 @ X18)
% 0.46/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.66  thf('131', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['129', '130'])).
% 0.46/0.66  thf('132', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i]:
% 0.46/0.66         (((k1_relat_1 @ X27) != (X26))
% 0.46/0.66          | (v1_partfun1 @ X27 @ X26)
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.66  thf('133', plain,
% 0.46/0.66      (![X27 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X27)
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ (k1_relat_1 @ X27))
% 0.46/0.66          | (v1_partfun1 @ X27 @ (k1_relat_1 @ X27)))),
% 0.46/0.66      inference('simplify', [status(thm)], ['132'])).
% 0.46/0.66  thf('134', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('sup-', [status(thm)], ['131', '133'])).
% 0.46/0.66  thf('135', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['134'])).
% 0.46/0.66  thf('136', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['125', '135'])).
% 0.46/0.66  thf('137', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['124', '136'])).
% 0.46/0.66  thf('138', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['137'])).
% 0.46/0.66  thf('139', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['123', '138'])).
% 0.46/0.66  thf('140', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.46/0.66  thf('141', plain,
% 0.46/0.66      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['122', '140'])).
% 0.46/0.66  thf('142', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('143', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('145', plain,
% 0.46/0.66      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['141', '142', '143', '144'])).
% 0.46/0.66  thf('146', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i]:
% 0.46/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.46/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.66  thf('147', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['145', '146'])).
% 0.46/0.66  thf('148', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('sup+', [status(thm)], ['120', '121'])).
% 0.46/0.66  thf('149', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('150', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('151', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf('152', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['129', '130'])).
% 0.46/0.66  thf('153', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['151', '152'])).
% 0.46/0.66  thf('154', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['150', '153'])).
% 0.46/0.66  thf('155', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['154'])).
% 0.46/0.66  thf('156', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['149', '155'])).
% 0.46/0.66  thf('157', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['156'])).
% 0.46/0.66  thf('158', plain,
% 0.46/0.66      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['148', '157'])).
% 0.46/0.66  thf('159', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('161', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('162', plain,
% 0.46/0.66      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['158', '159', '160', '161'])).
% 0.46/0.66  thf('163', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('demod', [status(thm)], ['147', '162'])).
% 0.46/0.66  thf('164', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['117', '163'])).
% 0.46/0.66  thf('165', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('166', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('167', plain,
% 0.46/0.66      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.46/0.66  thf('168', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.46/0.66      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.66  thf('169', plain,
% 0.46/0.66      (![X35 : $i, X36 : $i]:
% 0.46/0.66         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 0.46/0.66          | (v1_funct_2 @ X35 @ (k1_relat_1 @ X35) @ X36)
% 0.46/0.66          | ~ (v1_funct_1 @ X35)
% 0.46/0.66          | ~ (v1_relat_1 @ X35))),
% 0.46/0.66      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.46/0.66  thf('170', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['168', '169'])).
% 0.46/0.66  thf('171', plain,
% 0.46/0.66      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['167', '170'])).
% 0.46/0.66  thf('172', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['113'])).
% 0.46/0.66  thf('173', plain,
% 0.46/0.66      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66         (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['171', '172'])).
% 0.46/0.66  thf('174', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66           (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['116', '173'])).
% 0.46/0.66  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('176', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('177', plain,
% 0.46/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66        (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.46/0.66  thf('178', plain,
% 0.46/0.66      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66         (k1_relat_1 @ sk_C))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['115', '177'])).
% 0.46/0.66  thf('179', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('183', plain,
% 0.46/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66        (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['178', '179', '180', '181', '182'])).
% 0.46/0.66  thf('184', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('185', plain,
% 0.46/0.66      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.46/0.66  thf('186', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | (m1_subset_1 @ X0 @ 
% 0.46/0.66             (k1_zfmisc_1 @ 
% 0.46/0.66              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['127', '128'])).
% 0.46/0.66  thf('187', plain,
% 0.46/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.46/0.66         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.46/0.66          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.66  thf('188', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.46/0.66              = (k2_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['186', '187'])).
% 0.46/0.66  thf('189', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.66          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['185', '188'])).
% 0.46/0.66  thf('190', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['113'])).
% 0.46/0.66  thf('191', plain,
% 0.46/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.66          = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['189', '190'])).
% 0.46/0.66  thf('192', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66            (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.66            = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['184', '191'])).
% 0.46/0.66  thf('193', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('194', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('195', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ 
% 0.46/0.66         (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ (k2_funct_1 @ sk_C))
% 0.46/0.66         = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['192', '193', '194'])).
% 0.46/0.66  thf('196', plain,
% 0.46/0.66      (![X8 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.46/0.66          | ~ (v2_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_relat_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('197', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('198', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('199', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('200', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('201', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('202', plain,
% 0.46/0.66      (![X8 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.46/0.66          | ~ (v2_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_relat_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('203', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('204', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('205', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf('206', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.46/0.66  thf('207', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['205', '206'])).
% 0.46/0.66  thf('208', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['204', '207'])).
% 0.46/0.66  thf('209', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['208'])).
% 0.46/0.66  thf('210', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['203', '209'])).
% 0.46/0.66  thf('211', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['210'])).
% 0.46/0.66  thf('212', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['202', '211'])).
% 0.46/0.66  thf('213', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['212'])).
% 0.46/0.66  thf('214', plain,
% 0.46/0.66      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66         (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['201', '213'])).
% 0.46/0.66  thf('215', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('216', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('217', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('218', plain,
% 0.46/0.66      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['214', '215', '216', '217'])).
% 0.46/0.66  thf('219', plain,
% 0.46/0.66      (![X26 : $i, X27 : $i]:
% 0.46/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.46/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.46/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.46/0.66          | ~ (v1_relat_1 @ X27))),
% 0.46/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.46/0.66  thf('220', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.46/0.66             (k2_struct_0 @ sk_A))
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66            = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['218', '219'])).
% 0.46/0.66  thf('221', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.66  thf('222', plain,
% 0.46/0.66      (![X8 : $i]:
% 0.46/0.66         ((v2_funct_1 @ (k2_funct_1 @ X8))
% 0.46/0.66          | ~ (v2_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_funct_1 @ X8)
% 0.46/0.66          | ~ (v1_relat_1 @ X8))),
% 0.46/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.46/0.66  thf('223', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_funct_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('224', plain,
% 0.46/0.66      (![X7 : $i]:
% 0.46/0.66         ((v1_relat_1 @ (k2_funct_1 @ X7))
% 0.46/0.66          | ~ (v1_funct_1 @ X7)
% 0.46/0.66          | ~ (v1_relat_1 @ X7))),
% 0.46/0.66      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.46/0.66  thf('225', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k1_relat_1 @ X13) = (k2_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf('226', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['156'])).
% 0.46/0.66  thf('227', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['225', '226'])).
% 0.46/0.66  thf('228', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['224', '227'])).
% 0.46/0.66  thf('229', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['228'])).
% 0.46/0.66  thf('230', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['223', '229'])).
% 0.46/0.66  thf('231', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['230'])).
% 0.46/0.66  thf('232', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         (~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['222', '231'])).
% 0.46/0.66  thf('233', plain,
% 0.46/0.66      (![X0 : $i]:
% 0.46/0.66         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.46/0.66          | ~ (v2_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_funct_1 @ X0)
% 0.46/0.66          | ~ (v1_relat_1 @ X0))),
% 0.46/0.66      inference('simplify', [status(thm)], ['232'])).
% 0.46/0.66  thf('234', plain,
% 0.46/0.66      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup+', [status(thm)], ['221', '233'])).
% 0.46/0.66  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('236', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('237', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('238', plain,
% 0.46/0.66      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['234', '235', '236', '237'])).
% 0.46/0.66  thf('239', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66            = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['220', '238'])).
% 0.46/0.66  thf('240', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66            = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['200', '239'])).
% 0.46/0.66  thf('241', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66            = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['199', '240'])).
% 0.46/0.66  thf('242', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('243', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('244', plain,
% 0.46/0.66      ((((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66          = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['241', '242', '243'])).
% 0.46/0.66  thf('245', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66            = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['198', '244'])).
% 0.46/0.66  thf('246', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('247', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('248', plain,
% 0.46/0.66      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66         = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['245', '246', '247'])).
% 0.46/0.66  thf('249', plain,
% 0.46/0.66      (![X13 : $i]:
% 0.46/0.66         (~ (v2_funct_1 @ X13)
% 0.46/0.66          | ((k2_relat_1 @ X13) = (k1_relat_1 @ (k2_funct_1 @ X13)))
% 0.46/0.66          | ~ (v1_funct_1 @ X13)
% 0.46/0.66          | ~ (v1_relat_1 @ X13))),
% 0.46/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.46/0.66  thf('250', plain,
% 0.46/0.66      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('sup+', [status(thm)], ['248', '249'])).
% 0.46/0.66  thf('251', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.46/0.66      inference('simplify', [status(thm)], ['113'])).
% 0.46/0.66  thf('252', plain,
% 0.46/0.66      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.46/0.66        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['250', '251'])).
% 0.46/0.66  thf('253', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['197', '252'])).
% 0.46/0.66  thf('254', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('255', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('256', plain,
% 0.46/0.66      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['253', '254', '255'])).
% 0.46/0.66  thf('257', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('sup-', [status(thm)], ['196', '256'])).
% 0.46/0.66  thf('258', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('259', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('260', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('261', plain,
% 0.46/0.66      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['257', '258', '259', '260'])).
% 0.46/0.66  thf('262', plain,
% 0.46/0.66      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['257', '258', '259', '260'])).
% 0.46/0.66  thf('263', plain,
% 0.46/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.46/0.66      inference('demod', [status(thm)], ['195', '261', '262'])).
% 0.46/0.66  thf('264', plain,
% 0.46/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.46/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.46/0.66      inference('demod', [status(thm)], ['105', '114', '183', '263'])).
% 0.46/0.66  thf('265', plain,
% 0.46/0.66      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['264'])).
% 0.46/0.66  thf('266', plain,
% 0.46/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.46/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.46/0.66      inference('sup-', [status(thm)], ['94', '265'])).
% 0.46/0.66  thf('267', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('268', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('269', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('270', plain,
% 0.46/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.46/0.66         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.46/0.66      inference('demod', [status(thm)], ['266', '267', '268', '269'])).
% 0.46/0.66  thf('271', plain,
% 0.46/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.46/0.66          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['93', '270'])).
% 0.46/0.66  thf('272', plain,
% 0.46/0.66      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66           sk_C)
% 0.46/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['18', '271'])).
% 0.46/0.66  thf('273', plain,
% 0.46/0.66      ((m1_subset_1 @ sk_C @ 
% 0.46/0.66        (k1_zfmisc_1 @ 
% 0.46/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.46/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.46/0.66  thf(redefinition_r2_funct_2, axiom,
% 0.46/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.66         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.66       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.46/0.66  thf('274', plain,
% 0.46/0.66      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.66          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.46/0.66          | ~ (v1_funct_1 @ X28)
% 0.46/0.66          | ~ (v1_funct_1 @ X31)
% 0.46/0.66          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.46/0.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.66          | (r2_funct_2 @ X29 @ X30 @ X28 @ X31)
% 0.46/0.66          | ((X28) != (X31)))),
% 0.46/0.66      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.46/0.66  thf('275', plain,
% 0.46/0.66      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.66         ((r2_funct_2 @ X29 @ X30 @ X31 @ X31)
% 0.46/0.66          | ~ (v1_funct_1 @ X31)
% 0.46/0.66          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.46/0.66          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.46/0.66      inference('simplify', [status(thm)], ['274'])).
% 0.46/0.66  thf('276', plain,
% 0.46/0.66      ((~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.46/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.46/0.66        | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.46/0.66           sk_C))),
% 0.46/0.66      inference('sup-', [status(thm)], ['273', '275'])).
% 0.46/0.66  thf('277', plain,
% 0.46/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.46/0.66      inference('demod', [status(thm)], ['75', '76'])).
% 0.46/0.66  thf('278', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('279', plain,
% 0.46/0.66      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['276', '277', '278'])).
% 0.46/0.66  thf('280', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.46/0.66  thf('281', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('282', plain, ((v2_funct_1 @ sk_C)),
% 0.46/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.66  thf('283', plain, ($false),
% 0.46/0.66      inference('demod', [status(thm)], ['272', '279', '280', '281', '282'])).
% 0.46/0.66  
% 0.46/0.66  % SZS output end Refutation
% 0.46/0.66  
% 0.50/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
