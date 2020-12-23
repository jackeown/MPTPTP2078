%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yVQ7iOn3bm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:17 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 886 expanded)
%              Number of leaves         :   43 ( 277 expanded)
%              Depth                    :   21
%              Number of atoms          : 2188 (18927 expanded)
%              Number of equality atoms :  113 ( 538 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_relat_1 @ X6 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
    ! [X7: $i] :
      ( ~ ( v2_funct_1 @ X7 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X7 ) @ X7 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X8
        = ( k2_funct_1 @ X9 ) )
      | ( ( k5_relat_1 @ X9 @ X8 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ( ( k2_relat_1 @ X9 )
       != ( k1_relat_1 @ X8 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ ( k2_relat_1 @ X0 ) )
       != ( k6_relat_1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
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
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
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
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
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
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ ( k2_funct_1 @ X0 ) )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
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
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('43',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','40','43'])).

thf('45',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52','57'])).

thf('59',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('63',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','64'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('66',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('67',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','71'])).

thf('73',plain,(
    ! [X29: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('74',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('80',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('81',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','78','79','80'])).

thf('82',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

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

thf('87',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('92',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

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
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('97',plain,(
    ! [X28: $i] :
      ( ( ( k2_struct_0 @ X28 )
        = ( u1_struct_0 @ X28 ) )
      | ~ ( l1_struct_0 @ X28 ) ) ),
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
    inference(demod,[status(thm)],['88','89','94','95','104'])).

thf('106',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['81','106'])).

thf('108',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k1_relat_1 @ X6 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X6 ) ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X5 ) )
      | ~ ( v2_funct_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

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

thf('111',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('112',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('115',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('116',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k2_relset_1 @ X31 @ X30 @ X32 )
       != X30 )
      | ~ ( v2_funct_1 @ X32 )
      | ( ( k2_tops_2 @ X31 @ X30 @ X32 )
        = ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('122',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('123',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('126',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('127',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['123','124','125','126','127'])).

thf('129',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('131',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k2_relset_1 @ X27 @ X26 @ X25 )
       != X26 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X25 ) @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('132',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('135',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('136',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133','134','135','136'])).

thf('138',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('140',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('141',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','129','138','141'])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('145',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['108','147'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('150',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['38','39'])).

thf('151',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152'])).

thf('154',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['107','154'])).

thf('156',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','155'])).

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
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['156','157','158','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('162',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('163',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_funct_2 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('164',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['161','167'])).

thf('169',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('171',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['168','169','170'])).

thf('172',plain,(
    $false ),
    inference(demod,[status(thm)],['160','171'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yVQ7iOn3bm
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:06:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 475 iterations in 0.201s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.65  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.65  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.65  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.45/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.66  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.45/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.45/0.66  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.45/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.66  thf(t55_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) =>
% 0.45/0.66         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.45/0.66           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X6 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X6)
% 0.45/0.66          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | ~ (v1_relat_1 @ X6))),
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
% 0.45/0.66  thf(fc6_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.66         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.66         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X5 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.45/0.66          | ~ (v2_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X6 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X6)
% 0.45/0.66          | ((k2_relat_1 @ X6) = (k1_relat_1 @ (k2_funct_1 @ X6)))
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | ~ (v1_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf(t61_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) =>
% 0.45/0.66         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.45/0.66             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.45/0.66           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.45/0.66             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X7 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X7)
% 0.45/0.66          | ((k5_relat_1 @ (k2_funct_1 @ X7) @ X7)
% 0.45/0.66              = (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.45/0.66          | ~ (v1_funct_1 @ X7)
% 0.45/0.66          | ~ (v1_relat_1 @ X7))),
% 0.45/0.66      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.45/0.66  thf(t63_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66           ( ( ( v2_funct_1 @ A ) & 
% 0.45/0.66               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.45/0.66               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.45/0.66             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X8)
% 0.45/0.66          | ~ (v1_funct_1 @ X8)
% 0.45/0.66          | ((X8) = (k2_funct_1 @ X9))
% 0.45/0.66          | ((k5_relat_1 @ X9 @ X8) != (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.45/0.66          | ((k2_relat_1 @ X9) != (k1_relat_1 @ X8))
% 0.45/0.66          | ~ (v2_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_funct_1 @ X9)
% 0.45/0.66          | ~ (v1_relat_1 @ X9))),
% 0.45/0.66      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.45/0.66            != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ((k6_relat_1 @ (k2_relat_1 @ X0))
% 0.45/0.66              != (k6_relat_1 @ (k1_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k6_relat_1 @ (k2_relat_1 @ X0)) != (k6_relat_1 @ (k2_relat_1 @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '8'])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['3', '10'])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['13'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ((k2_relat_1 @ (k2_funct_1 @ X0)) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['15'])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.45/0.66          | ~ (v2_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.66  thf(d3_struct_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
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
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66           sk_C)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66           sk_C)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['19', '24'])).
% 0.45/0.66  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['25', '26'])).
% 0.45/0.66  thf('28', plain,
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
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.45/0.66          | (v1_partfun1 @ X16 @ X17)
% 0.45/0.66          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.45/0.66          | ~ (v1_funct_1 @ X16)
% 0.45/0.66          | (v1_xboole_0 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.66  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.45/0.66  thf(d4_partfun1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.45/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i]:
% 0.45/0.66         (~ (v1_partfun1 @ X20 @ X19)
% 0.45/0.66          | ((k1_relat_1 @ X20) = (X19))
% 0.45/0.66          | ~ (v4_relat_1 @ X20 @ X19)
% 0.45/0.66          | ~ (v1_relat_1 @ X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['33', '34'])).
% 0.45/0.66  thf('36', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc2_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.45/0.66          | (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ 
% 0.45/0.66           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.45/0.66        | (v1_relat_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.66  thf(fc6_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.66  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(cc2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.45/0.66  thf('42', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.66         ((v4_relat_1 @ X10 @ X11)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.66  thf('43', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['41', '42'])).
% 0.45/0.66  thf('44', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['35', '40', '43'])).
% 0.45/0.66  thf('45', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_C @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['45', '46'])).
% 0.45/0.66  thf('48', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.45/0.66          | (v1_partfun1 @ X16 @ X17)
% 0.45/0.66          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.45/0.66          | ~ (v1_funct_1 @ X16)
% 0.45/0.66          | (v1_xboole_0 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.45/0.66  thf('51', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.66  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('53', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('54', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('55', plain,
% 0.45/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup+', [status(thm)], ['53', '54'])).
% 0.45/0.66  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['51', '52', '57'])).
% 0.45/0.66  thf('59', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i]:
% 0.45/0.66         (~ (v1_partfun1 @ X20 @ X19)
% 0.45/0.66          | ((k1_relat_1 @ X20) = (X19))
% 0.45/0.66          | ~ (v4_relat_1 @ X20 @ X19)
% 0.45/0.66          | ~ (v1_relat_1 @ X20))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.45/0.66  thf('60', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['58', '59'])).
% 0.45/0.66  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('63', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.45/0.66         ((v4_relat_1 @ X10 @ X11)
% 0.45/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.45/0.66  thf('64', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.66  thf('65', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['60', '61', '64'])).
% 0.45/0.66  thf(fc2_struct_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.66       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.66  thf('66', plain,
% 0.45/0.66      (![X29 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.45/0.66          | ~ (l1_struct_0 @ X29)
% 0.45/0.66          | (v2_struct_0 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.45/0.66        | (v2_struct_0 @ sk_B)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.66  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('69', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['67', '68'])).
% 0.45/0.66  thf('70', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('71', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['69', '70'])).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.45/0.66        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['44', '71'])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (![X29 : $i]:
% 0.45/0.66         (~ (v1_xboole_0 @ (u1_struct_0 @ X29))
% 0.45/0.66          | ~ (l1_struct_0 @ X29)
% 0.45/0.66          | (v2_struct_0 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.66  thf('74', plain,
% 0.45/0.66      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.45/0.66        | (v2_struct_0 @ sk_B)
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.66  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('76', plain,
% 0.45/0.66      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['74', '75'])).
% 0.45/0.66  thf('77', plain, (~ (v2_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('78', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('79', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('80', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['27', '78', '79', '80'])).
% 0.45/0.66  thf('82', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('84', plain,
% 0.45/0.66      (((m1_subset_1 @ sk_C @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['82', '83'])).
% 0.45/0.66  thf('85', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf(d4_tops_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.45/0.66         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 0.45/0.66          | ~ (v2_funct_1 @ X32)
% 0.45/0.66          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 0.45/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.66          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.45/0.66          | ~ (v1_funct_1 @ X32))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.66  thf('88', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            = (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['86', '87'])).
% 0.45/0.66  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['90', '91'])).
% 0.45/0.66  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('94', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('95', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('96', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.66  thf('97', plain,
% 0.45/0.66      (![X28 : $i]:
% 0.45/0.66         (((k2_struct_0 @ X28) = (u1_struct_0 @ X28)) | ~ (l1_struct_0 @ X28))),
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
% 0.45/0.66      inference('demod', [status(thm)], ['88', '89', '94', '95', '104'])).
% 0.45/0.66  thf('106', plain,
% 0.45/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['105'])).
% 0.45/0.66  thf('107', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66           (k2_funct_1 @ sk_C)) @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['81', '106'])).
% 0.45/0.66  thf('108', plain,
% 0.45/0.66      (![X6 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X6)
% 0.45/0.66          | ((k1_relat_1 @ X6) = (k2_relat_1 @ (k2_funct_1 @ X6)))
% 0.45/0.66          | ~ (v1_funct_1 @ X6)
% 0.45/0.66          | ~ (v1_relat_1 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.45/0.66  thf('109', plain,
% 0.45/0.66      (![X5 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k2_funct_1 @ X5))
% 0.45/0.66          | ~ (v2_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_funct_1 @ X5)
% 0.45/0.66          | ~ (v1_relat_1 @ X5))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.66  thf('110', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf(t31_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.66         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.66           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.66           ( m1_subset_1 @
% 0.45/0.66             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('111', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X25)
% 0.45/0.66          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 0.45/0.66          | (m1_subset_1 @ (k2_funct_1 @ X25) @ 
% 0.45/0.66             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.45/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.66          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 0.45/0.66          | ~ (v1_funct_1 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.66  thf('112', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66           (k1_zfmisc_1 @ 
% 0.45/0.66            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['110', '111'])).
% 0.45/0.66  thf('113', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('114', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('115', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('116', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('117', plain,
% 0.45/0.66      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['112', '113', '114', '115', '116'])).
% 0.45/0.66  thf('118', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['117'])).
% 0.45/0.66  thf('119', plain,
% 0.45/0.66      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X31 @ X30 @ X32) != (X30))
% 0.45/0.66          | ~ (v2_funct_1 @ X32)
% 0.45/0.66          | ((k2_tops_2 @ X31 @ X30 @ X32) = (k2_funct_1 @ X32))
% 0.45/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30)))
% 0.45/0.66          | ~ (v1_funct_2 @ X32 @ X31 @ X30)
% 0.45/0.66          | ~ (v1_funct_1 @ X32))),
% 0.45/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.45/0.66  thf('120', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66             (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['118', '119'])).
% 0.45/0.66  thf('121', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf('122', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X25)
% 0.45/0.66          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 0.45/0.66          | (v1_funct_1 @ (k2_funct_1 @ X25))
% 0.45/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.66          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 0.45/0.66          | ~ (v1_funct_1 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.66  thf('123', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['121', '122'])).
% 0.45/0.66  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('125', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('126', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('127', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('128', plain,
% 0.45/0.66      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['123', '124', '125', '126', '127'])).
% 0.45/0.66  thf('129', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.45/0.66      inference('simplify', [status(thm)], ['128'])).
% 0.45/0.66  thf('130', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['84', '85'])).
% 0.45/0.66  thf('131', plain,
% 0.45/0.66      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X25)
% 0.45/0.66          | ((k2_relset_1 @ X27 @ X26 @ X25) != (X26))
% 0.45/0.66          | (v1_funct_2 @ (k2_funct_1 @ X25) @ X26 @ X27)
% 0.45/0.66          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.45/0.66          | ~ (v1_funct_2 @ X25 @ X27 @ X26)
% 0.45/0.66          | ~ (v1_funct_1 @ X25))),
% 0.45/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.45/0.66  thf('132', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.45/0.66        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66           (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66            != (k2_struct_0 @ sk_B))
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['130', '131'])).
% 0.45/0.66  thf('133', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('134', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.45/0.66  thf('135', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.45/0.66         = (k2_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['102', '103'])).
% 0.45/0.66  thf('136', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('137', plain,
% 0.45/0.66      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66         (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['132', '133', '134', '135', '136'])).
% 0.45/0.66  thf('138', plain,
% 0.45/0.66      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.45/0.66        (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('simplify', [status(thm)], ['137'])).
% 0.45/0.66  thf('139', plain,
% 0.45/0.66      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.45/0.66      inference('simplify', [status(thm)], ['117'])).
% 0.45/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('140', plain,
% 0.45/0.66      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.45/0.66          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.66  thf('141', plain,
% 0.45/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['139', '140'])).
% 0.45/0.66  thf('142', plain,
% 0.45/0.66      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.66        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['120', '129', '138', '141'])).
% 0.45/0.66  thf('143', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['109', '142'])).
% 0.45/0.66  thf('144', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('145', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('147', plain,
% 0.45/0.66      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 0.45/0.66  thf('148', plain,
% 0.45/0.66      ((((k1_relat_1 @ sk_C) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['108', '147'])).
% 0.45/0.66  thf('149', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.45/0.66      inference('clc', [status(thm)], ['69', '70'])).
% 0.45/0.66  thf('150', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('151', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('152', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('153', plain,
% 0.45/0.66      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.66        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.66      inference('demod', [status(thm)], ['148', '149', '150', '151', '152'])).
% 0.45/0.66  thf('154', plain,
% 0.45/0.66      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.45/0.66         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['153'])).
% 0.45/0.66  thf('155', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.45/0.66          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['107', '154'])).
% 0.45/0.66  thf('156', plain,
% 0.45/0.66      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66           sk_C)
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['18', '155'])).
% 0.45/0.66  thf('157', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('158', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('160', plain,
% 0.45/0.66      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66          sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['156', '157', '158', '159'])).
% 0.45/0.66  thf('161', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf('162', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ 
% 0.45/0.66        (k1_zfmisc_1 @ 
% 0.45/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.66  thf(reflexivity_r2_funct_2, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.45/0.66         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.45/0.66         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.66       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.45/0.66  thf('163', plain,
% 0.45/0.66      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.66         ((r2_funct_2 @ X21 @ X22 @ X23 @ X23)
% 0.45/0.66          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.45/0.66          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.45/0.66          | ~ (v1_funct_1 @ X23)
% 0.45/0.66          | ~ (v1_funct_1 @ X24)
% 0.45/0.66          | ~ (v1_funct_2 @ X24 @ X21 @ X22)
% 0.45/0.66          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.45/0.66      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.45/0.66  thf('164', plain,
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
% 0.45/0.66      inference('sup-', [status(thm)], ['162', '163'])).
% 0.45/0.66  thf('165', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('166', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('167', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X0 @ 
% 0.45/0.66             (k1_zfmisc_1 @ 
% 0.45/0.66              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.45/0.66          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.45/0.66          | ~ (v1_funct_1 @ X0)
% 0.45/0.66          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.45/0.66             sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['164', '165', '166'])).
% 0.45/0.66  thf('168', plain,
% 0.45/0.66      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['161', '167'])).
% 0.45/0.66  thf('169', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('170', plain,
% 0.45/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('171', plain,
% 0.45/0.66      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.45/0.66      inference('demod', [status(thm)], ['168', '169', '170'])).
% 0.45/0.66  thf('172', plain, ($false), inference('demod', [status(thm)], ['160', '171'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
