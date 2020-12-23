%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZuN67LFbOn

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:14 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  319 (1494 expanded)
%              Number of leaves         :   44 ( 455 expanded)
%              Depth                    :   31
%              Number of atoms          : 3202 (31476 expanded)
%              Number of equality atoms :  135 ( 873 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('4',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
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
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k5_relat_1 @ X21 @ ( k2_funct_1 @ X21 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ( X22
        = ( k2_funct_1 @ X23 ) )
      | ( ( k5_relat_1 @ X22 @ X23 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X23 ) ) )
      | ( ( k2_relat_1 @ X22 )
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v2_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
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
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
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

thf('23',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k2_relset_1 @ X46 @ X45 @ X47 )
       != X45 )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_tops_2 @ X46 @ X45 @ X47 )
        = ( k2_funct_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('40',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('43',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('49',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','46','47','52'])).

thf('54',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['32','57'])).

thf('59',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('63',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

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

thf('68',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_funct_1 @ X39 )
      | ( ( k2_relset_1 @ X41 @ X40 @ X39 )
       != X40 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X39 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('69',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('73',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X43: $i] :
      ( ( ( k2_struct_0 @ X43 )
        = ( u1_struct_0 @ X43 ) )
      | ~ ( l1_struct_0 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('78',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['69','70','75','80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k2_relset_1 @ X46 @ X45 @ X47 )
       != X45 )
      | ~ ( v2_funct_1 @ X47 )
      | ( ( k2_tops_2 @ X46 @ X45 @ X47 )
        = ( k2_funct_1 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('85',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('87',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v2_funct_1 @ X39 )
      | ( ( k2_relset_1 @ X41 @ X40 @ X39 )
       != X40 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X41 @ X40 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('88',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('91',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('92',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92'])).

thf('94',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('96',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('101',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('103',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('104',plain,(
    ! [X42: $i] :
      ( ( v1_funct_2 @ X42 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['100','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['99','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('114',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('116',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('117',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['112','117','118','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('122',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('123',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('126',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('127',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X34 @ X33 )
      | ( ( k1_relat_1 @ X34 )
        = X33 )
      | ~ ( v4_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('128',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('130',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('131',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('132',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['128','129','132'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('134',plain,(
    ! [X44: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('135',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['120','139'])).

thf('141',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['85','94','140'])).

thf('142',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('143',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('144',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('146',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('147',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('148',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('149',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('150',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('151',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('153',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('155',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('156',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('157',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('158',plain,(
    ! [X42: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X42 ) @ ( k2_relat_1 @ X42 ) ) ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('159',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k1_relat_1 @ X34 )
       != X33 )
      | ( v1_partfun1 @ X34 @ X33 )
      | ~ ( v4_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('162',plain,(
    ! [X34: $i] :
      ( ~ ( v1_relat_1 @ X34 )
      | ~ ( v4_relat_1 @ X34 @ ( k1_relat_1 @ X34 ) )
      | ( v1_partfun1 @ X34 @ ( k1_relat_1 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['160','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['157','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['156','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['155','167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['154','169'])).

thf('171',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['153','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('173',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('176',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('177',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['171','172','173','174','175','176'])).

thf('178',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['178','179','180','181'])).

thf('183',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X34 @ X33 )
      | ( ( k1_relat_1 @ X34 )
        = X33 )
      | ~ ( v4_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('184',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('186',plain,(
    ! [X13: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X13 ) )
      | ~ ( v2_funct_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('187',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('188',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('189',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('190',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('191',plain,(
    ! [X12: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    ! [X20: $i] :
      ( ~ ( v2_funct_1 @ X20 )
      | ( ( k2_relat_1 @ X20 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X20 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('193',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['189','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['188','199'])).

thf('201',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['187','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['186','203'])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['185','205'])).

thf('207',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('208',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207','208','209'])).

thf('211',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['184','210'])).

thf('212',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['147','211'])).

thf('213',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('214',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('215',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['212','213','214'])).

thf('216',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['146','215'])).

thf('217',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('218',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['93'])).

thf('219',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['216','217','218'])).

thf('220',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','219'])).

thf('221',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('222',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['220','221','222','223'])).

thf('225',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','224'])).

thf('226',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['141','225'])).

thf('227',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','227'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['228','229','230','231'])).

thf('233',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['61','232'])).

thf('234',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','233'])).

thf('235',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('236',plain,(
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

thf('237',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( r2_funct_2 @ X35 @ X36 @ X37 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( v1_partfun1 @ X30 @ X31 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('244',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['244','245','246'])).

thf('248',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X34 @ X33 )
      | ( ( k1_relat_1 @ X34 )
        = X33 )
      | ~ ( v4_relat_1 @ X34 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('249',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('251',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('253',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['249','250','253'])).

thf('255',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('256',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X44: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X44 ) )
      | ~ ( l1_struct_0 @ X44 )
      | ( v2_struct_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('258',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['256','257'])).

thf('259',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('260',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('263',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('264',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['260','261'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['241','262','263','264'])).

thf('266',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['235','265'])).

thf('267',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('269',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['266','267','268'])).

thf('270',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['115','116'])).

thf('271',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('272',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    $false ),
    inference(demod,[status(thm)],['234','269','270','271','272'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZuN67LFbOn
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/1.01  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.74/1.01  % Solved by: fo/fo7.sh
% 0.74/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/1.01  % done 1044 iterations in 0.564s
% 0.74/1.01  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.74/1.01  % SZS output start Refutation
% 0.74/1.01  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.74/1.01  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.74/1.01  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.74/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/1.01  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.74/1.01  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.74/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/1.01  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.74/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.74/1.01  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.74/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/1.01  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.74/1.01  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.74/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.74/1.01  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.74/1.01  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.74/1.01  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.74/1.01  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.74/1.01  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.74/1.01  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.74/1.01  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.74/1.01  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.74/1.01  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.74/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.74/1.01  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.74/1.01  thf(t55_funct_1, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/1.01       ( ( v2_funct_1 @ A ) =>
% 0.74/1.01         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.74/1.01           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.74/1.01  thf('0', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf(dt_k2_funct_1, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/1.01       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.74/1.01         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.74/1.01  thf('1', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('2', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf(fc6_funct_1, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.74/1.01       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.74/1.01         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.74/1.01         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.74/1.01  thf('3', plain,
% 0.74/1.01      (![X13 : $i]:
% 0.74/1.01         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.74/1.01          | ~ (v2_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_relat_1 @ X13))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.74/1.01  thf('4', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf(t61_funct_1, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/1.01       ( ( v2_funct_1 @ A ) =>
% 0.74/1.01         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 0.74/1.01             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 0.74/1.01           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 0.74/1.01             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.74/1.01  thf('5', plain,
% 0.74/1.01      (![X21 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X21)
% 0.74/1.01          | ((k5_relat_1 @ X21 @ (k2_funct_1 @ X21))
% 0.74/1.01              = (k6_relat_1 @ (k1_relat_1 @ X21)))
% 0.74/1.01          | ~ (v1_funct_1 @ X21)
% 0.74/1.01          | ~ (v1_relat_1 @ X21))),
% 0.74/1.01      inference('cnf', [status(esa)], [t61_funct_1])).
% 0.74/1.01  thf(t64_funct_1, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/1.01       ( ![B:$i]:
% 0.74/1.01         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.74/1.01           ( ( ( v2_funct_1 @ A ) & 
% 0.74/1.01               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.74/1.01               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.74/1.01             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.74/1.01  thf('6', plain,
% 0.74/1.01      (![X22 : $i, X23 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X22)
% 0.74/1.01          | ~ (v1_funct_1 @ X22)
% 0.74/1.01          | ((X22) = (k2_funct_1 @ X23))
% 0.74/1.01          | ((k5_relat_1 @ X22 @ X23) != (k6_relat_1 @ (k2_relat_1 @ X23)))
% 0.74/1.01          | ((k2_relat_1 @ X22) != (k1_relat_1 @ X23))
% 0.74/1.01          | ~ (v2_funct_1 @ X23)
% 0.74/1.01          | ~ (v1_funct_1 @ X23)
% 0.74/1.01          | ~ (v1_relat_1 @ X23))),
% 0.74/1.01      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.74/1.01  thf('7', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.74/1.01            != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['5', '6'])).
% 0.74/1.01  thf('8', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ((k6_relat_1 @ (k1_relat_1 @ X0))
% 0.74/1.01              != (k6_relat_1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.74/1.01      inference('simplify', [status(thm)], ['7'])).
% 0.74/1.01  thf('9', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((k6_relat_1 @ (k1_relat_1 @ X0)) != (k6_relat_1 @ (k1_relat_1 @ X0)))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.74/1.01      inference('sup-', [status(thm)], ['4', '8'])).
% 0.74/1.01  thf('10', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['9'])).
% 0.74/1.01  thf('11', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.74/1.01      inference('sup-', [status(thm)], ['3', '10'])).
% 0.74/1.01  thf('12', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['11'])).
% 0.74/1.01  thf('13', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.74/1.01      inference('sup-', [status(thm)], ['2', '12'])).
% 0.74/1.01  thf('14', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['13'])).
% 0.74/1.01  thf('15', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.74/1.01      inference('sup-', [status(thm)], ['1', '14'])).
% 0.74/1.01  thf('16', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['15'])).
% 0.74/1.01  thf('17', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.74/1.01      inference('sup-', [status(thm)], ['0', '16'])).
% 0.74/1.01  thf('18', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['17'])).
% 0.74/1.01  thf(d3_struct_0, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.74/1.01  thf('19', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('20', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('21', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('22', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf(t64_tops_2, conjecture,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( l1_struct_0 @ A ) =>
% 0.74/1.01       ( ![B:$i]:
% 0.74/1.01         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.74/1.01           ( ![C:$i]:
% 0.74/1.01             ( ( ( v1_funct_1 @ C ) & 
% 0.74/1.01                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.74/1.01                 ( m1_subset_1 @
% 0.74/1.01                   C @ 
% 0.74/1.01                   ( k1_zfmisc_1 @
% 0.74/1.01                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.74/1.01               ( ( ( ( k2_relset_1 @
% 0.74/1.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.74/1.01                     ( k2_struct_0 @ B ) ) & 
% 0.74/1.01                   ( v2_funct_1 @ C ) ) =>
% 0.74/1.01                 ( r2_funct_2 @
% 0.74/1.01                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.74/1.01                   ( k2_tops_2 @
% 0.74/1.01                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.74/1.01                     ( k2_tops_2 @
% 0.74/1.01                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.74/1.01                   C ) ) ) ) ) ) ))).
% 0.74/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.74/1.01    (~( ![A:$i]:
% 0.74/1.01        ( ( l1_struct_0 @ A ) =>
% 0.74/1.01          ( ![B:$i]:
% 0.74/1.01            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.74/1.01              ( ![C:$i]:
% 0.74/1.01                ( ( ( v1_funct_1 @ C ) & 
% 0.74/1.01                    ( v1_funct_2 @
% 0.74/1.01                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.74/1.01                    ( m1_subset_1 @
% 0.74/1.01                      C @ 
% 0.74/1.01                      ( k1_zfmisc_1 @
% 0.74/1.01                        ( k2_zfmisc_1 @
% 0.74/1.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.74/1.01                  ( ( ( ( k2_relset_1 @
% 0.74/1.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.74/1.01                        ( k2_struct_0 @ B ) ) & 
% 0.74/1.01                      ( v2_funct_1 @ C ) ) =>
% 0.74/1.01                    ( r2_funct_2 @
% 0.74/1.01                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.74/1.01                      ( k2_tops_2 @
% 0.74/1.01                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.74/1.01                        ( k2_tops_2 @
% 0.74/1.01                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.74/1.01                      C ) ) ) ) ) ) ) )),
% 0.74/1.01    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.74/1.01  thf('23', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.74/1.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01          sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('24', plain,
% 0.74/1.01      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01           sk_C)
% 0.74/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup-', [status(thm)], ['22', '23'])).
% 0.74/1.01  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('26', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.74/1.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01          sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['24', '25'])).
% 0.74/1.01  thf('27', plain,
% 0.74/1.01      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01           sk_C)
% 0.74/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup-', [status(thm)], ['21', '26'])).
% 0.74/1.01  thf('28', plain, ((l1_struct_0 @ sk_A)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('29', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01          sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['27', '28'])).
% 0.74/1.01  thf('30', plain,
% 0.74/1.01      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01           sk_C)
% 0.74/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup-', [status(thm)], ['20', '29'])).
% 0.74/1.01  thf('31', plain, ((l1_struct_0 @ sk_A)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('32', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.74/1.01          sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['30', '31'])).
% 0.74/1.01  thf('33', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('34', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('35', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('36', plain,
% 0.74/1.01      (((m1_subset_1 @ sk_C @ 
% 0.74/1.01         (k1_zfmisc_1 @ 
% 0.74/1.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup+', [status(thm)], ['34', '35'])).
% 0.74/1.01  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('38', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.74/1.01  thf(d4_tops_2, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/1.01       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.74/1.01         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.74/1.01  thf('39', plain,
% 0.74/1.01      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.74/1.01         (((k2_relset_1 @ X46 @ X45 @ X47) != (X45))
% 0.74/1.01          | ~ (v2_funct_1 @ X47)
% 0.74/1.01          | ((k2_tops_2 @ X46 @ X45 @ X47) = (k2_funct_1 @ X47))
% 0.74/1.01          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.74/1.01          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.74/1.01          | ~ (v1_funct_1 @ X47))),
% 0.74/1.01      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.74/1.01  thf('40', plain,
% 0.74/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01            = (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.74/1.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01            != (u1_struct_0 @ sk_B)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['38', '39'])).
% 0.74/1.01  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('42', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('43', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('44', plain,
% 0.74/1.01      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup+', [status(thm)], ['42', '43'])).
% 0.74/1.01  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('46', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['44', '45'])).
% 0.74/1.01  thf('47', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('48', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('49', plain,
% 0.74/1.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('50', plain,
% 0.74/1.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01          = (k2_struct_0 @ sk_B))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup+', [status(thm)], ['48', '49'])).
% 0.74/1.01  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('52', plain,
% 0.74/1.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['50', '51'])).
% 0.74/1.01  thf('53', plain,
% 0.74/1.01      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01          = (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_struct_0 @ sk_B) != (u1_struct_0 @ sk_B)))),
% 0.74/1.01      inference('demod', [status(thm)], ['40', '41', '46', '47', '52'])).
% 0.74/1.01  thf('54', plain,
% 0.74/1.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B)
% 0.74/1.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01            = (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['33', '53'])).
% 0.74/1.01  thf('55', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('56', plain,
% 0.74/1.01      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.74/1.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01            = (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('demod', [status(thm)], ['54', '55'])).
% 0.74/1.01  thf('57', plain,
% 0.74/1.01      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('simplify', [status(thm)], ['56'])).
% 0.74/1.01  thf('58', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01           (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01          sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['32', '57'])).
% 0.74/1.01  thf('59', plain,
% 0.74/1.01      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01           sk_C)
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup-', [status(thm)], ['19', '58'])).
% 0.74/1.01  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('61', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01           (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01          sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['59', '60'])).
% 0.74/1.01  thf('62', plain,
% 0.74/1.01      (![X13 : $i]:
% 0.74/1.01         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.74/1.01          | ~ (v2_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_relat_1 @ X13))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.74/1.01  thf('63', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('64', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.74/1.01  thf('65', plain,
% 0.74/1.01      (((m1_subset_1 @ sk_C @ 
% 0.74/1.01         (k1_zfmisc_1 @ 
% 0.74/1.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup+', [status(thm)], ['63', '64'])).
% 0.74/1.01  thf('66', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('67', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.74/1.01  thf(t31_funct_2, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/1.01       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.74/1.01         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.74/1.01           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.74/1.01           ( m1_subset_1 @
% 0.74/1.01             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.74/1.01  thf('68', plain,
% 0.74/1.01      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X39)
% 0.74/1.01          | ((k2_relset_1 @ X41 @ X40 @ X39) != (X40))
% 0.74/1.01          | (m1_subset_1 @ (k2_funct_1 @ X39) @ 
% 0.74/1.01             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.74/1.01          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.74/1.01          | ~ (v1_funct_2 @ X39 @ X41 @ X40)
% 0.74/1.01          | ~ (v1_funct_1 @ X39))),
% 0.74/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.74/1.01  thf('69', plain,
% 0.74/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.74/1.01        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.74/1.01           (k1_zfmisc_1 @ 
% 0.74/1.01            (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.74/1.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01            != (k2_struct_0 @ sk_B))
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['67', '68'])).
% 0.74/1.01  thf('70', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('71', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('72', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['44', '45'])).
% 0.74/1.01  thf('73', plain,
% 0.74/1.01      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup+', [status(thm)], ['71', '72'])).
% 0.74/1.01  thf('74', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('75', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/1.01  thf('76', plain,
% 0.74/1.01      (![X43 : $i]:
% 0.74/1.01         (((k2_struct_0 @ X43) = (u1_struct_0 @ X43)) | ~ (l1_struct_0 @ X43))),
% 0.74/1.01      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/1.01  thf('77', plain,
% 0.74/1.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['50', '51'])).
% 0.74/1.01  thf('78', plain,
% 0.74/1.01      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01          = (k2_struct_0 @ sk_B))
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup+', [status(thm)], ['76', '77'])).
% 0.74/1.01  thf('79', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('80', plain,
% 0.74/1.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['78', '79'])).
% 0.74/1.01  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('82', plain,
% 0.74/1.01      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.74/1.01         (k1_zfmisc_1 @ 
% 0.74/1.01          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.74/1.01        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.74/1.01      inference('demod', [status(thm)], ['69', '70', '75', '80', '81'])).
% 0.74/1.01  thf('83', plain,
% 0.74/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.74/1.01      inference('simplify', [status(thm)], ['82'])).
% 0.74/1.01  thf('84', plain,
% 0.74/1.01      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.74/1.01         (((k2_relset_1 @ X46 @ X45 @ X47) != (X45))
% 0.74/1.01          | ~ (v2_funct_1 @ X47)
% 0.74/1.01          | ((k2_tops_2 @ X46 @ X45 @ X47) = (k2_funct_1 @ X47))
% 0.74/1.01          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 0.74/1.01          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.74/1.01          | ~ (v1_funct_1 @ X47))),
% 0.74/1.01      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.74/1.01  thf('85', plain,
% 0.74/1.01      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.74/1.01             (k2_struct_0 @ sk_A))
% 0.74/1.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['83', '84'])).
% 0.74/1.01  thf('86', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['65', '66'])).
% 0.74/1.01  thf('87', plain,
% 0.74/1.01      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X39)
% 0.74/1.01          | ((k2_relset_1 @ X41 @ X40 @ X39) != (X40))
% 0.74/1.01          | (v1_funct_1 @ (k2_funct_1 @ X39))
% 0.74/1.01          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 0.74/1.01          | ~ (v1_funct_2 @ X39 @ X41 @ X40)
% 0.74/1.01          | ~ (v1_funct_1 @ X39))),
% 0.74/1.01      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.74/1.01  thf('88', plain,
% 0.74/1.01      ((~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.74/1.01        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01            != (k2_struct_0 @ sk_B))
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['86', '87'])).
% 0.74/1.01  thf('89', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('90', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['73', '74'])).
% 0.74/1.01  thf('91', plain,
% 0.74/1.01      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['78', '79'])).
% 0.74/1.01  thf('92', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('93', plain,
% 0.74/1.01      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.74/1.01      inference('demod', [status(thm)], ['88', '89', '90', '91', '92'])).
% 0.74/1.01  thf('94', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('simplify', [status(thm)], ['93'])).
% 0.74/1.01  thf('95', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf(redefinition_k2_relset_1, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/1.01       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.74/1.01  thf('96', plain,
% 0.74/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.74/1.01         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.74/1.01          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.74/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/1.01  thf('97', plain,
% 0.74/1.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_relat_1 @ sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['95', '96'])).
% 0.74/1.01  thf('98', plain,
% 0.74/1.01      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.74/1.01         = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup+', [status(thm)], ['97', '98'])).
% 0.74/1.01  thf('100', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf('101', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('102', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('103', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf(t3_funct_2, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.74/1.01       ( ( v1_funct_1 @ A ) & 
% 0.74/1.01         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.74/1.01         ( m1_subset_1 @
% 0.74/1.01           A @ 
% 0.74/1.01           ( k1_zfmisc_1 @
% 0.74/1.01             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.74/1.01  thf('104', plain,
% 0.74/1.01      (![X42 : $i]:
% 0.74/1.01         ((v1_funct_2 @ X42 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))
% 0.74/1.01          | ~ (v1_funct_1 @ X42)
% 0.74/1.01          | ~ (v1_relat_1 @ X42))),
% 0.74/1.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.74/1.01  thf('105', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.74/1.01           (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['103', '104'])).
% 0.74/1.01  thf('106', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.74/1.01             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['102', '105'])).
% 0.74/1.01  thf('107', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.74/1.01           (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['106'])).
% 0.74/1.01  thf('108', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | (v1_funct_2 @ (k2_funct_1 @ X0) @ 
% 0.74/1.01             (k1_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['101', '107'])).
% 0.74/1.01  thf('109', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.74/1.01           (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['108'])).
% 0.74/1.01  thf('110', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.74/1.01           (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0))),
% 0.74/1.01      inference('sup+', [status(thm)], ['100', '109'])).
% 0.74/1.01  thf('111', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 0.74/1.01             (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('simplify', [status(thm)], ['110'])).
% 0.74/1.01  thf('112', plain,
% 0.74/1.01      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.74/1.01         (k1_relat_1 @ sk_C))
% 0.74/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.74/1.01      inference('sup+', [status(thm)], ['99', '111'])).
% 0.74/1.01  thf('113', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf(cc2_relat_1, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( v1_relat_1 @ A ) =>
% 0.74/1.01       ( ![B:$i]:
% 0.74/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.74/1.01  thf('114', plain,
% 0.74/1.01      (![X3 : $i, X4 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.74/1.01          | (v1_relat_1 @ X3)
% 0.74/1.01          | ~ (v1_relat_1 @ X4))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/1.01  thf('115', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ 
% 0.74/1.01           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.74/1.01        | (v1_relat_1 @ sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['113', '114'])).
% 0.74/1.01  thf(fc6_relat_1, axiom,
% 0.74/1.01    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.74/1.01  thf('116', plain,
% 0.74/1.01      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/1.01  thf('117', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('118', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('119', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('120', plain,
% 0.74/1.01      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.74/1.01        (k1_relat_1 @ sk_C))),
% 0.74/1.01      inference('demod', [status(thm)], ['112', '117', '118', '119'])).
% 0.74/1.01  thf('121', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.74/1.01  thf(cc5_funct_2, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.74/1.01       ( ![C:$i]:
% 0.74/1.01         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/1.01           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.74/1.01             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.74/1.01  thf('122', plain,
% 0.74/1.01      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.74/1.01          | (v1_partfun1 @ X30 @ X31)
% 0.74/1.01          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.74/1.01          | ~ (v1_funct_1 @ X30)
% 0.74/1.01          | (v1_xboole_0 @ X32))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.74/1.01  thf('123', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['121', '122'])).
% 0.74/1.01  thf('124', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('125', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['44', '45'])).
% 0.74/1.01  thf('126', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | (v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.74/1.01  thf(d4_partfun1, axiom,
% 0.74/1.01    (![A:$i,B:$i]:
% 0.74/1.01     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.74/1.01       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.74/1.01  thf('127', plain,
% 0.74/1.01      (![X33 : $i, X34 : $i]:
% 0.74/1.01         (~ (v1_partfun1 @ X34 @ X33)
% 0.74/1.01          | ((k1_relat_1 @ X34) = (X33))
% 0.74/1.01          | ~ (v4_relat_1 @ X34 @ X33)
% 0.74/1.01          | ~ (v1_relat_1 @ X34))),
% 0.74/1.01      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.74/1.01  thf('128', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.74/1.01        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['126', '127'])).
% 0.74/1.01  thf('129', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('130', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.74/1.01  thf(cc2_relset_1, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i]:
% 0.74/1.01     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.74/1.01       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.74/1.01  thf('131', plain,
% 0.74/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.74/1.01         ((v4_relat_1 @ X24 @ X25)
% 0.74/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/1.01  thf('132', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup-', [status(thm)], ['130', '131'])).
% 0.74/1.01  thf('133', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['128', '129', '132'])).
% 0.74/1.01  thf(fc2_struct_0, axiom,
% 0.74/1.01    (![A:$i]:
% 0.74/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.74/1.01       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.74/1.01  thf('134', plain,
% 0.74/1.01      (![X44 : $i]:
% 0.74/1.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X44))
% 0.74/1.01          | ~ (l1_struct_0 @ X44)
% 0.74/1.01          | (v2_struct_0 @ X44))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.74/1.01  thf('135', plain,
% 0.74/1.01      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))
% 0.74/1.01        | (v2_struct_0 @ sk_B)
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup-', [status(thm)], ['133', '134'])).
% 0.74/1.01  thf('136', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('137', plain,
% 0.74/1.01      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['135', '136'])).
% 0.74/1.01  thf('138', plain, (~ (v2_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('139', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['137', '138'])).
% 0.74/1.01  thf('140', plain,
% 0.74/1.01      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.74/1.01        (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('demod', [status(thm)], ['120', '139'])).
% 0.74/1.01  thf('141', plain,
% 0.74/1.01      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_funct_1 @ sk_C)) != (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['85', '94', '140'])).
% 0.74/1.01  thf('142', plain,
% 0.74/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.74/1.01      inference('simplify', [status(thm)], ['82'])).
% 0.74/1.01  thf('143', plain,
% 0.74/1.01      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.74/1.01         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.74/1.01          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.74/1.01      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.74/1.01  thf('144', plain,
% 0.74/1.01      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['142', '143'])).
% 0.74/1.01  thf('145', plain,
% 0.74/1.01      (![X13 : $i]:
% 0.74/1.01         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.74/1.01          | ~ (v2_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_relat_1 @ X13))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.74/1.01  thf('146', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf('147', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('148', plain,
% 0.74/1.01      (![X13 : $i]:
% 0.74/1.01         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.74/1.01          | ~ (v2_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_relat_1 @ X13))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.74/1.01  thf('149', plain,
% 0.74/1.01      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.74/1.01      inference('simplify', [status(thm)], ['82'])).
% 0.74/1.01  thf('150', plain,
% 0.74/1.01      (![X3 : $i, X4 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.74/1.01          | (v1_relat_1 @ X3)
% 0.74/1.01          | ~ (v1_relat_1 @ X4))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.74/1.01  thf('151', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ 
% 0.74/1.01           (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A)))
% 0.74/1.01        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['149', '150'])).
% 0.74/1.01  thf('152', plain,
% 0.74/1.01      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.74/1.01  thf('153', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('demod', [status(thm)], ['151', '152'])).
% 0.74/1.01  thf('154', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf('155', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('156', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('157', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf('158', plain,
% 0.74/1.01      (![X42 : $i]:
% 0.74/1.01         ((m1_subset_1 @ X42 @ 
% 0.74/1.01           (k1_zfmisc_1 @ 
% 0.74/1.01            (k2_zfmisc_1 @ (k1_relat_1 @ X42) @ (k2_relat_1 @ X42))))
% 0.74/1.01          | ~ (v1_funct_1 @ X42)
% 0.74/1.01          | ~ (v1_relat_1 @ X42))),
% 0.74/1.01      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.74/1.01  thf('159', plain,
% 0.74/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.74/1.01         ((v4_relat_1 @ X24 @ X25)
% 0.74/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/1.01  thf('160', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['158', '159'])).
% 0.74/1.01  thf('161', plain,
% 0.74/1.01      (![X33 : $i, X34 : $i]:
% 0.74/1.01         (((k1_relat_1 @ X34) != (X33))
% 0.74/1.01          | (v1_partfun1 @ X34 @ X33)
% 0.74/1.01          | ~ (v4_relat_1 @ X34 @ X33)
% 0.74/1.01          | ~ (v1_relat_1 @ X34))),
% 0.74/1.01      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.74/1.01  thf('162', plain,
% 0.74/1.01      (![X34 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X34)
% 0.74/1.01          | ~ (v4_relat_1 @ X34 @ (k1_relat_1 @ X34))
% 0.74/1.01          | (v1_partfun1 @ X34 @ (k1_relat_1 @ X34)))),
% 0.74/1.01      inference('simplify', [status(thm)], ['161'])).
% 0.74/1.01  thf('163', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('sup-', [status(thm)], ['160', '162'])).
% 0.74/1.01  thf('164', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['163'])).
% 0.74/1.01  thf('165', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['157', '164'])).
% 0.74/1.01  thf('166', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['156', '165'])).
% 0.74/1.01  thf('167', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['166'])).
% 0.74/1.01  thf('168', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['155', '167'])).
% 0.74/1.01  thf('169', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['168'])).
% 0.74/1.01  thf('170', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['154', '169'])).
% 0.74/1.01  thf('171', plain,
% 0.74/1.01      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01           (k1_relat_1 @ sk_C)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['153', '170'])).
% 0.74/1.01  thf('172', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('simplify', [status(thm)], ['93'])).
% 0.74/1.01  thf('173', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('175', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('176', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['137', '138'])).
% 0.74/1.01  thf('177', plain,
% 0.74/1.01      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01           (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)],
% 0.74/1.01                ['171', '172', '173', '174', '175', '176'])).
% 0.74/1.01  thf('178', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.74/1.01        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01           (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['148', '177'])).
% 0.74/1.01  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('181', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('182', plain,
% 0.74/1.01      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('demod', [status(thm)], ['178', '179', '180', '181'])).
% 0.74/1.01  thf('183', plain,
% 0.74/1.01      (![X33 : $i, X34 : $i]:
% 0.74/1.01         (~ (v1_partfun1 @ X34 @ X33)
% 0.74/1.01          | ((k1_relat_1 @ X34) = (X33))
% 0.74/1.01          | ~ (v4_relat_1 @ X34 @ X33)
% 0.74/1.01          | ~ (v1_relat_1 @ X34))),
% 0.74/1.01      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.74/1.01  thf('184', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01        | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.74/1.01             (k2_struct_0 @ sk_A))
% 0.74/1.01        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01            = (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['182', '183'])).
% 0.74/1.01  thf('185', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['137', '138'])).
% 0.74/1.01  thf('186', plain,
% 0.74/1.01      (![X13 : $i]:
% 0.74/1.01         ((v2_funct_1 @ (k2_funct_1 @ X13))
% 0.74/1.01          | ~ (v2_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_funct_1 @ X13)
% 0.74/1.01          | ~ (v1_relat_1 @ X13))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.74/1.01  thf('187', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('188', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('189', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k1_relat_1 @ X20) = (k2_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf('190', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_relat_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('191', plain,
% 0.74/1.01      (![X12 : $i]:
% 0.74/1.01         ((v1_funct_1 @ (k2_funct_1 @ X12))
% 0.74/1.01          | ~ (v1_funct_1 @ X12)
% 0.74/1.01          | ~ (v1_relat_1 @ X12))),
% 0.74/1.01      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.74/1.01  thf('192', plain,
% 0.74/1.01      (![X20 : $i]:
% 0.74/1.01         (~ (v2_funct_1 @ X20)
% 0.74/1.01          | ((k2_relat_1 @ X20) = (k1_relat_1 @ (k2_funct_1 @ X20)))
% 0.74/1.01          | ~ (v1_funct_1 @ X20)
% 0.74/1.01          | ~ (v1_relat_1 @ X20))),
% 0.74/1.01      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.74/1.01  thf('193', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['158', '159'])).
% 0.74/1.01  thf('194', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['192', '193'])).
% 0.74/1.01  thf('195', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['191', '194'])).
% 0.74/1.01  thf('196', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['195'])).
% 0.74/1.01  thf('197', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['190', '196'])).
% 0.74/1.01  thf('198', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['197'])).
% 0.74/1.01  thf('199', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['189', '198'])).
% 0.74/1.01  thf('200', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['188', '199'])).
% 0.74/1.01  thf('201', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['200'])).
% 0.74/1.01  thf('202', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['187', '201'])).
% 0.74/1.01  thf('203', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['202'])).
% 0.74/1.01  thf('204', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['186', '203'])).
% 0.74/1.01  thf('205', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.74/1.01          | ~ (v2_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_relat_1 @ X0))),
% 0.74/1.01      inference('simplify', [status(thm)], ['204'])).
% 0.74/1.01  thf('206', plain,
% 0.74/1.01      (((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))
% 0.74/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.74/1.01      inference('sup+', [status(thm)], ['185', '205'])).
% 0.74/1.01  thf('207', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('208', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('209', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('210', plain,
% 0.74/1.01      ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('demod', [status(thm)], ['206', '207', '208', '209'])).
% 0.74/1.01  thf('211', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01            = (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['184', '210'])).
% 0.74/1.01  thf('212', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01            = (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['147', '211'])).
% 0.74/1.01  thf('213', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('demod', [status(thm)], ['151', '152'])).
% 0.74/1.01  thf('214', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('simplify', [status(thm)], ['93'])).
% 0.74/1.01  thf('215', plain,
% 0.74/1.01      (((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01         = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('demod', [status(thm)], ['212', '213', '214'])).
% 0.74/1.01  thf('216', plain,
% 0.74/1.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.74/1.01        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('sup+', [status(thm)], ['146', '215'])).
% 0.74/1.01  thf('217', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('demod', [status(thm)], ['151', '152'])).
% 0.74/1.01  thf('218', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.74/1.01      inference('simplify', [status(thm)], ['93'])).
% 0.74/1.01  thf('219', plain,
% 0.74/1.01      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.74/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('demod', [status(thm)], ['216', '217', '218'])).
% 0.74/1.01  thf('220', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.74/1.01        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['145', '219'])).
% 0.74/1.01  thf('221', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('222', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('223', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('224', plain,
% 0.74/1.01      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('demod', [status(thm)], ['220', '221', '222', '223'])).
% 0.74/1.01  thf('225', plain,
% 0.74/1.01      (((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01         (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('demod', [status(thm)], ['144', '224'])).
% 0.74/1.01  thf('226', plain,
% 0.74/1.01      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.74/1.01        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['141', '225'])).
% 0.74/1.01  thf('227', plain,
% 0.74/1.01      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.74/1.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.74/1.01      inference('simplify', [status(thm)], ['226'])).
% 0.74/1.01  thf('228', plain,
% 0.74/1.01      ((~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C)
% 0.74/1.01        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.74/1.01      inference('sup-', [status(thm)], ['62', '227'])).
% 0.74/1.01  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('232', plain,
% 0.74/1.01      (((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.74/1.01         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.74/1.01      inference('demod', [status(thm)], ['228', '229', '230', '231'])).
% 0.74/1.01  thf('233', plain,
% 0.74/1.01      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.74/1.01          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['61', '232'])).
% 0.74/1.01  thf('234', plain,
% 0.74/1.01      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.74/1.01           sk_C)
% 0.74/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v2_funct_1 @ sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['18', '233'])).
% 0.74/1.01  thf('235', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('demod', [status(thm)], ['36', '37'])).
% 0.74/1.01  thf('236', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf(reflexivity_r2_funct_2, axiom,
% 0.74/1.01    (![A:$i,B:$i,C:$i,D:$i]:
% 0.74/1.01     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.74/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.74/1.01         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.74/1.01         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.74/1.01       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.74/1.01  thf('237', plain,
% 0.74/1.01      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.74/1.01         ((r2_funct_2 @ X35 @ X36 @ X37 @ X37)
% 0.74/1.01          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.74/1.01          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.74/1.01          | ~ (v1_funct_1 @ X37)
% 0.74/1.01          | ~ (v1_funct_1 @ X38)
% 0.74/1.01          | ~ (v1_funct_2 @ X38 @ X35 @ X36)
% 0.74/1.01          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.74/1.01      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.74/1.01  thf('238', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X0 @ 
% 0.74/1.01             (k1_zfmisc_1 @ 
% 0.74/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.74/1.01          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.74/1.01             sk_C))),
% 0.74/1.01      inference('sup-', [status(thm)], ['236', '237'])).
% 0.74/1.01  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('240', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('241', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X0 @ 
% 0.74/1.01             (k1_zfmisc_1 @ 
% 0.74/1.01              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.74/1.01          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.74/1.01             sk_C))),
% 0.74/1.01      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.74/1.01  thf('242', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('243', plain,
% 0.74/1.01      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.74/1.01          | (v1_partfun1 @ X30 @ X31)
% 0.74/1.01          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.74/1.01          | ~ (v1_funct_1 @ X30)
% 0.74/1.01          | (v1_xboole_0 @ X32))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.74/1.01  thf('244', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['242', '243'])).
% 0.74/1.01  thf('245', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('246', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('247', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['244', '245', '246'])).
% 0.74/1.01  thf('248', plain,
% 0.74/1.01      (![X33 : $i, X34 : $i]:
% 0.74/1.01         (~ (v1_partfun1 @ X34 @ X33)
% 0.74/1.01          | ((k1_relat_1 @ X34) = (X33))
% 0.74/1.01          | ~ (v4_relat_1 @ X34 @ X33)
% 0.74/1.01          | ~ (v1_relat_1 @ X34))),
% 0.74/1.01      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.74/1.01  thf('249', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ~ (v1_relat_1 @ sk_C)
% 0.74/1.01        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.74/1.01        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['247', '248'])).
% 0.74/1.01  thf('250', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('251', plain,
% 0.74/1.01      ((m1_subset_1 @ sk_C @ 
% 0.74/1.01        (k1_zfmisc_1 @ 
% 0.74/1.01         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('252', plain,
% 0.74/1.01      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.74/1.01         ((v4_relat_1 @ X24 @ X25)
% 0.74/1.01          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.74/1.01      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.74/1.01  thf('253', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.74/1.01      inference('sup-', [status(thm)], ['251', '252'])).
% 0.74/1.01  thf('254', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['249', '250', '253'])).
% 0.74/1.01  thf('255', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['137', '138'])).
% 0.74/1.01  thf('256', plain,
% 0.74/1.01      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.74/1.01        | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))),
% 0.74/1.01      inference('demod', [status(thm)], ['254', '255'])).
% 0.74/1.01  thf('257', plain,
% 0.74/1.01      (![X44 : $i]:
% 0.74/1.01         (~ (v1_xboole_0 @ (u1_struct_0 @ X44))
% 0.74/1.01          | ~ (l1_struct_0 @ X44)
% 0.74/1.01          | (v2_struct_0 @ X44))),
% 0.74/1.01      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.74/1.01  thf('258', plain,
% 0.74/1.01      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))
% 0.74/1.01        | (v2_struct_0 @ sk_B)
% 0.74/1.01        | ~ (l1_struct_0 @ sk_B))),
% 0.74/1.01      inference('sup-', [status(thm)], ['256', '257'])).
% 0.74/1.01  thf('259', plain, ((l1_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('260', plain,
% 0.74/1.01      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['258', '259'])).
% 0.74/1.01  thf('261', plain, (~ (v2_struct_0 @ sk_B)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('262', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['260', '261'])).
% 0.74/1.01  thf('263', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['260', '261'])).
% 0.74/1.01  thf('264', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.74/1.01      inference('clc', [status(thm)], ['260', '261'])).
% 0.74/1.01  thf('265', plain,
% 0.74/1.01      (![X0 : $i]:
% 0.74/1.01         (~ (m1_subset_1 @ X0 @ 
% 0.74/1.01             (k1_zfmisc_1 @ 
% 0.74/1.01              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.74/1.01          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.74/1.01          | ~ (v1_funct_1 @ X0)
% 0.74/1.01          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.74/1.01             sk_C))),
% 0.74/1.01      inference('demod', [status(thm)], ['241', '262', '263', '264'])).
% 0.74/1.01  thf('266', plain,
% 0.74/1.01      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.74/1.01        | ~ (v1_funct_1 @ sk_C)
% 0.74/1.01        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.74/1.01      inference('sup-', [status(thm)], ['235', '265'])).
% 0.74/1.01  thf('267', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('268', plain,
% 0.74/1.01      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.74/1.01      inference('demod', [status(thm)], ['44', '45'])).
% 0.74/1.01  thf('269', plain,
% 0.74/1.01      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['266', '267', '268'])).
% 0.74/1.01  thf('270', plain, ((v1_relat_1 @ sk_C)),
% 0.74/1.01      inference('demod', [status(thm)], ['115', '116'])).
% 0.74/1.01  thf('271', plain, ((v1_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('272', plain, ((v2_funct_1 @ sk_C)),
% 0.74/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/1.01  thf('273', plain, ($false),
% 0.74/1.01      inference('demod', [status(thm)], ['234', '269', '270', '271', '272'])).
% 0.74/1.01  
% 0.74/1.01  % SZS output end Refutation
% 0.74/1.01  
% 0.86/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
