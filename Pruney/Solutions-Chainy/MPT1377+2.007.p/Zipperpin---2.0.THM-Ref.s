%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.99lRgkp2lK

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  199 (2997 expanded)
%              Number of leaves         :   26 ( 857 expanded)
%              Depth                    :   30
%              Number of atoms          : 3186 (50295 expanded)
%              Number of equality atoms :   77 (1224 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t33_compts_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v2_compts_1 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
        <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v2_compts_1 @ B @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
          <=> ( ( v2_compts_1 @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_compts_1])).

thf('0',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_u1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_subset_1 @ ( u1_pre_topc @ A ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
        & ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X8: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('9',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t12_compts_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( B = k1_xboole_0 )
             => ( ( v2_compts_1 @ B @ A )
              <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) )
            & ( ( v2_pre_topc @ A )
             => ( ( B = k1_xboole_0 )
                | ( ( v2_compts_1 @ B @ A )
                <=> ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_pre_topc @ X17 )
      | ( X16 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X17 @ X16 ) )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('13',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t66_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) )
             => ( ( B = C )
               => ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) )
                  = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ C ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X13 != X15 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X13 ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ X14 @ X13 ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) ) ) )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t66_pre_topc])).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ X14 @ X15 ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ X14 @ X15 ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X14 ) @ ( u1_pre_topc @ X14 ) ) @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('25',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( ( g1_pre_topc @ X11 @ X12 )
       != ( g1_pre_topc @ X9 @ X10 ) )
      | ( X11 = X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('34',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','36'])).

thf('38',plain,
    ( ( ( ( k1_pre_topc @ sk_A @ sk_B )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['14','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('41',plain,
    ( ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('45',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('49',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('50',plain,
    ( ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','47','52'])).

thf('54',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','53'])).

thf('55',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','54'])).

thf('56',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('64',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_pre_topc @ X17 )
      | ( X16 = k1_xboole_0 )
      | ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('65',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','68'])).

thf('70',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('74',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X16 != k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X17 @ X16 ) )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('76',plain,(
    ! [X17: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X17 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X17 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('79',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('80',plain,
    ( ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['77','80'])).

thf('82',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('83',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','47','52'])).

thf('84',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('86',plain,
    ( ( ( k1_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('90',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X16 != k1_xboole_0 )
      | ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('92',plain,(
    ! [X17: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X17 @ k1_xboole_0 ) )
      | ( v2_compts_1 @ k1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('97',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('98',plain,
    ( ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['95','98'])).

thf('100',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['87','99'])).

thf('101',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('105',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('106',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('108',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('110',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_pre_topc @ X17 )
      | ( X16 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X17 @ X16 ) )
      | ~ ( v2_compts_1 @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('111',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,(
    ! [X8: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X8 ) @ ( u1_pre_topc @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 )
      | ~ ( v2_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('118',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('119',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v2_pre_topc @ X17 )
      | ( X16 = k1_xboole_0 )
      | ( v2_compts_1 @ X16 @ X17 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X17 @ X16 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('120',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','47','52'])).

thf('122',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['117','122'])).

thf('124',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['116','125'])).

thf('127',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['115','129'])).

thf('131',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('133',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('135',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X17: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X17 @ k1_xboole_0 ) )
      | ( v2_compts_1 @ k1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('137',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('139',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','47','52'])).

thf('140',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('142',plain,
    ( ( ( k1_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('144',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('145',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X17: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X17 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X17 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('147',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('149',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['148','149'])).

thf('151',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['147','150','151'])).

thf('153',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['137','142','152'])).

thf('154',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('155',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('156',plain,
    ( ~ ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['153','156'])).

thf('158',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['107','157'])).

thf('159',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['161'])).

thf('163',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('166',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('167',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','103','106','160','162','170'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.99lRgkp2lK
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.64  % Solved by: fo/fo7.sh
% 0.20/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.64  % done 403 iterations in 0.214s
% 0.20/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.64  % SZS output start Refutation
% 0.20/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.64  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.64  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.20/0.64  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.64  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.20/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.64  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.64  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.64  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.20/0.64  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.64  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.20/0.64  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.20/0.64  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.64  thf(t33_compts_1, conjecture,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.64       ( ![B:$i]:
% 0.20/0.64         ( ( ( v2_compts_1 @ B @ A ) & 
% 0.20/0.64             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.20/0.64           ( ( v2_compts_1 @
% 0.20/0.64               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.64             ( m1_subset_1 @
% 0.20/0.64               B @ 
% 0.20/0.64               ( k1_zfmisc_1 @
% 0.20/0.64                 ( u1_struct_0 @
% 0.20/0.64                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.64    (~( ![A:$i]:
% 0.20/0.64        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.64            ( l1_pre_topc @ A ) ) =>
% 0.20/0.64          ( ![B:$i]:
% 0.20/0.64            ( ( ( v2_compts_1 @ B @ A ) & 
% 0.20/0.64                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.20/0.64              ( ( v2_compts_1 @
% 0.20/0.64                  B @ 
% 0.20/0.64                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.64                ( m1_subset_1 @
% 0.20/0.64                  B @ 
% 0.20/0.64                  ( k1_zfmisc_1 @
% 0.20/0.64                    ( u1_struct_0 @
% 0.20/0.64                      ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 0.20/0.64    inference('cnf.neg', [status(esa)], [t33_compts_1])).
% 0.20/0.64  thf('0', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64        | (v2_compts_1 @ sk_B @ sk_A))),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('1', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.20/0.64       ((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.20/0.64      inference('split', [status(esa)], ['0'])).
% 0.20/0.64  thf('2', plain,
% 0.20/0.64      ((~ (m1_subset_1 @ sk_B @ 
% 0.20/0.64           (k1_zfmisc_1 @ 
% 0.20/0.64            (u1_struct_0 @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64        | ~ (v2_compts_1 @ sk_B @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.64        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('3', plain,
% 0.20/0.64      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.20/0.64       ~
% 0.20/0.64       ((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.64       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.64       ~
% 0.20/0.64       ((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf(dt_u1_pre_topc, axiom,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( l1_pre_topc @ A ) =>
% 0.20/0.64       ( m1_subset_1 @
% 0.20/0.64         ( u1_pre_topc @ A ) @ 
% 0.20/0.64         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.64  thf('4', plain,
% 0.20/0.64      (![X7 : $i]:
% 0.20/0.64         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.20/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.64          | ~ (l1_pre_topc @ X7))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.64  thf(dt_g1_pre_topc, axiom,
% 0.20/0.64    (![A:$i,B:$i]:
% 0.20/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.64       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.20/0.64         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.20/0.64  thf('5', plain,
% 0.20/0.64      (![X1 : $i, X2 : $i]:
% 0.20/0.64         ((l1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.20/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.64  thf('6', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | (l1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.64  thf('7', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | (l1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.64  thf(fc6_pre_topc, axiom,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.64       ( ( v1_pre_topc @
% 0.20/0.64           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.20/0.64         ( v2_pre_topc @
% 0.20/0.64           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.64  thf('8', plain,
% 0.20/0.64      (![X8 : $i]:
% 0.20/0.64         ((v2_pre_topc @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.20/0.64          | ~ (l1_pre_topc @ X8)
% 0.20/0.64          | ~ (v2_pre_topc @ X8))),
% 0.20/0.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.20/0.64  thf('9', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.64      inference('split', [status(esa)], ['0'])).
% 0.20/0.64  thf('10', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64        | (v2_compts_1 @ sk_B @ sk_A))),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('11', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['10'])).
% 0.20/0.64  thf(t12_compts_1, axiom,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( l1_pre_topc @ A ) =>
% 0.20/0.64       ( ![B:$i]:
% 0.20/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.64           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.64               ( ( v2_compts_1 @ B @ A ) <=>
% 0.20/0.64                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 0.20/0.64             ( ( v2_pre_topc @ A ) =>
% 0.20/0.64               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.64                 ( ( v2_compts_1 @ B @ A ) <=>
% 0.20/0.64                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.64  thf('12', plain,
% 0.20/0.64      (![X16 : $i, X17 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.64          | ~ (v2_pre_topc @ X17)
% 0.20/0.64          | ((X16) = (k1_xboole_0))
% 0.20/0.64          | (v1_compts_1 @ (k1_pre_topc @ X17 @ X16))
% 0.20/0.64          | ~ (v2_compts_1 @ X16 @ X17)
% 0.20/0.64          | ~ (l1_pre_topc @ X17))),
% 0.20/0.64      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.64  thf('13', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v2_compts_1 @ sk_B @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | (v1_compts_1 @ 
% 0.20/0.64            (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ~ (v2_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.64  thf(abstractness_v1_pre_topc, axiom,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( l1_pre_topc @ A ) =>
% 0.20/0.64       ( ( v1_pre_topc @ A ) =>
% 0.20/0.64         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.20/0.64  thf('14', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (v1_pre_topc @ X0)
% 0.20/0.64          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.64          | ~ (l1_pre_topc @ X0))),
% 0.20/0.64      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.64  thf('15', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['10'])).
% 0.20/0.64  thf(t66_pre_topc, axiom,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( l1_pre_topc @ A ) =>
% 0.20/0.64       ( ![B:$i]:
% 0.20/0.64         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.64           ( ![C:$i]:
% 0.20/0.64             ( ( m1_subset_1 @
% 0.20/0.64                 C @ 
% 0.20/0.64                 ( k1_zfmisc_1 @
% 0.20/0.64                   ( u1_struct_0 @
% 0.20/0.64                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) =>
% 0.20/0.64               ( ( ( B ) = ( C ) ) =>
% 0.20/0.64                 ( ( g1_pre_topc @
% 0.20/0.64                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 0.20/0.64                     ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) ) =
% 0.20/0.64                   ( k1_pre_topc @
% 0.20/0.64                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 0.20/0.64                     C ) ) ) ) ) ) ) ))).
% 0.20/0.64  thf('16', plain,
% 0.20/0.64      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.20/0.64          | ((X13) != (X15))
% 0.20/0.64          | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ X14 @ X13)) @ 
% 0.20/0.64              (u1_pre_topc @ (k1_pre_topc @ X14 @ X13)))
% 0.20/0.64              = (k1_pre_topc @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)) @ 
% 0.20/0.64                 X15))
% 0.20/0.64          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))))
% 0.20/0.64          | ~ (l1_pre_topc @ X14))),
% 0.20/0.64      inference('cnf', [status(esa)], [t66_pre_topc])).
% 0.20/0.64  thf('17', plain,
% 0.20/0.64      (![X14 : $i, X15 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X14)
% 0.20/0.64          | ~ (m1_subset_1 @ X15 @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)))))
% 0.20/0.64          | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ X14 @ X15)) @ 
% 0.20/0.64              (u1_pre_topc @ (k1_pre_topc @ X14 @ X15)))
% 0.20/0.64              = (k1_pre_topc @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ X14) @ (u1_pre_topc @ X14)) @ 
% 0.20/0.64                 X15))
% 0.20/0.64          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.64  thf('18', plain,
% 0.20/0.64      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.64         | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.64             (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.64             = (k1_pre_topc @ 
% 0.20/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64                sk_B))
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['15', '17'])).
% 0.20/0.64  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('20', plain,
% 0.20/0.64      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.64         | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.64             (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.64             = (k1_pre_topc @ 
% 0.20/0.64                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64                sk_B))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.64  thf('21', plain,
% 0.20/0.64      (![X7 : $i]:
% 0.20/0.64         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.20/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.64          | ~ (l1_pre_topc @ X7))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.64  thf('22', plain,
% 0.20/0.64      (![X1 : $i, X2 : $i]:
% 0.20/0.64         ((v1_pre_topc @ (g1_pre_topc @ X1 @ X2))
% 0.20/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X1))))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.20/0.64  thf('23', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | (v1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.64  thf('24', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (v1_pre_topc @ X0)
% 0.20/0.64          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.64          | ~ (l1_pre_topc @ X0))),
% 0.20/0.64      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.20/0.64  thf('25', plain,
% 0.20/0.64      (![X7 : $i]:
% 0.20/0.64         ((m1_subset_1 @ (u1_pre_topc @ X7) @ 
% 0.20/0.64           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7))))
% 0.20/0.64          | ~ (l1_pre_topc @ X7))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.20/0.64  thf(free_g1_pre_topc, axiom,
% 0.20/0.64    (![A:$i,B:$i]:
% 0.20/0.64     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.64       ( ![C:$i,D:$i]:
% 0.20/0.64         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.20/0.64           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.64  thf('26', plain,
% 0.20/0.64      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.64         (((g1_pre_topc @ X11 @ X12) != (g1_pre_topc @ X9 @ X10))
% 0.20/0.64          | ((X11) = (X9))
% 0.20/0.64          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.20/0.64      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.20/0.64  thf('27', plain,
% 0.20/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.64          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.20/0.64              != (g1_pre_topc @ X1 @ X2)))),
% 0.20/0.64      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.64  thf('28', plain,
% 0.20/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.64         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.20/0.64          | ~ (l1_pre_topc @ X0)
% 0.20/0.64          | ~ (v1_pre_topc @ X0)
% 0.20/0.64          | ((u1_struct_0 @ X0) = (X2))
% 0.20/0.64          | ~ (l1_pre_topc @ X0))),
% 0.20/0.64      inference('sup-', [status(thm)], ['24', '27'])).
% 0.20/0.64  thf('29', plain,
% 0.20/0.64      (![X1 : $i, X2 : $i]:
% 0.20/0.64         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.20/0.64          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.20/0.64          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.20/0.64      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.64  thf('30', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | ~ (l1_pre_topc @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.64          | ((u1_struct_0 @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.64              = (u1_struct_0 @ X0)))),
% 0.20/0.64      inference('sup-', [status(thm)], ['23', '29'])).
% 0.20/0.64  thf('31', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | (l1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.64  thf('32', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (((u1_struct_0 @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.64            = (u1_struct_0 @ X0))
% 0.20/0.64          | ~ (l1_pre_topc @ X0))),
% 0.20/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.64  thf('33', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['10'])).
% 0.20/0.64  thf('34', plain,
% 0.20/0.64      ((((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.64  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('36', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('37', plain,
% 0.20/0.64      ((((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 0.20/0.64          (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['20', '36'])).
% 0.20/0.64  thf('38', plain,
% 0.20/0.64      (((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64           = (k1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64              sk_B))
% 0.20/0.64         | ~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['14', '37'])).
% 0.20/0.64  thf('39', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf(dt_k1_pre_topc, axiom,
% 0.20/0.64    (![A:$i,B:$i]:
% 0.20/0.64     ( ( ( l1_pre_topc @ A ) & 
% 0.20/0.64         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.64       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.20/0.64         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.20/0.64  thf('40', plain,
% 0.20/0.64      (![X3 : $i, X4 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X3)
% 0.20/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.64          | (m1_pre_topc @ (k1_pre_topc @ X3 @ X4) @ X3))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.64  thf('41', plain,
% 0.20/0.64      ((((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.64  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('43', plain,
% 0.20/0.64      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.64  thf(dt_m1_pre_topc, axiom,
% 0.20/0.64    (![A:$i]:
% 0.20/0.64     ( ( l1_pre_topc @ A ) =>
% 0.20/0.64       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.64  thf('44', plain,
% 0.20/0.64      (![X5 : $i, X6 : $i]:
% 0.20/0.64         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.64  thf('45', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.64  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('47', plain,
% 0.20/0.64      (((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.64  thf('48', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('49', plain,
% 0.20/0.64      (![X3 : $i, X4 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X3)
% 0.20/0.64          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.20/0.64          | (v1_pre_topc @ (k1_pre_topc @ X3 @ X4)))),
% 0.20/0.64      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.20/0.64  thf('50', plain,
% 0.20/0.64      ((((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.64  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('52', plain,
% 0.20/0.64      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.64  thf('53', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['38', '47', '52'])).
% 0.20/0.64  thf('54', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v2_compts_1 @ sk_B @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ~ (v2_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['13', '53'])).
% 0.20/0.64  thf('55', plain,
% 0.20/0.64      (((~ (v2_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['9', '54'])).
% 0.20/0.64  thf('56', plain,
% 0.20/0.64      (((~ (v2_pre_topc @ sk_A)
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['8', '55'])).
% 0.20/0.64  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('59', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.20/0.64  thf('60', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['7', '59'])).
% 0.20/0.64  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('62', plain,
% 0.20/0.64      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['60', '61'])).
% 0.20/0.64  thf('63', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('64', plain,
% 0.20/0.64      (![X16 : $i, X17 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.64          | ~ (v2_pre_topc @ X17)
% 0.20/0.64          | ((X16) = (k1_xboole_0))
% 0.20/0.64          | (v2_compts_1 @ X16 @ X17)
% 0.20/0.64          | ~ (v1_compts_1 @ (k1_pre_topc @ X17 @ X16))
% 0.20/0.64          | ~ (l1_pre_topc @ X17))),
% 0.20/0.64      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.64  thf('65', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ~ (v2_pre_topc @ sk_A)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['63', '64'])).
% 0.20/0.64  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('68', plain,
% 0.20/0.64      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.20/0.64  thf('69', plain,
% 0.20/0.64      (((((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ sk_A)))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['62', '68'])).
% 0.20/0.64  thf('70', plain,
% 0.20/0.64      ((((v2_compts_1 @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.64  thf('71', plain,
% 0.20/0.64      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf('72', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.64  thf('73', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['10'])).
% 0.20/0.64  thf('74', plain,
% 0.20/0.64      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['72', '73'])).
% 0.20/0.64  thf('75', plain,
% 0.20/0.64      (![X16 : $i, X17 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.64          | ((X16) != (k1_xboole_0))
% 0.20/0.64          | (v1_compts_1 @ (k1_pre_topc @ X17 @ X16))
% 0.20/0.64          | ~ (v2_compts_1 @ X16 @ X17)
% 0.20/0.64          | ~ (l1_pre_topc @ X17))),
% 0.20/0.64      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.64  thf('76', plain,
% 0.20/0.64      (![X17 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X17)
% 0.20/0.64          | ~ (v2_compts_1 @ k1_xboole_0 @ X17)
% 0.20/0.64          | (v1_compts_1 @ (k1_pre_topc @ X17 @ k1_xboole_0))
% 0.20/0.64          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.64  thf('77', plain,
% 0.20/0.64      ((((v1_compts_1 @ 
% 0.20/0.64          (k1_pre_topc @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64           k1_xboole_0))
% 0.20/0.64         | ~ (v2_compts_1 @ k1_xboole_0 @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['74', '76'])).
% 0.20/0.64  thf('78', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.64  thf('79', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.64      inference('split', [status(esa)], ['0'])).
% 0.20/0.64  thf('80', plain,
% 0.20/0.64      (((v2_compts_1 @ k1_xboole_0 @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['78', '79'])).
% 0.20/0.64  thf('81', plain,
% 0.20/0.64      ((((v1_compts_1 @ 
% 0.20/0.64          (k1_pre_topc @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64           k1_xboole_0))
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['77', '80'])).
% 0.20/0.64  thf('82', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.64  thf('83', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['38', '47', '52'])).
% 0.20/0.64  thf('84', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64             k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['82', '83'])).
% 0.20/0.64  thf('85', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.64  thf('86', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ k1_xboole_0)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64             k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['84', '85'])).
% 0.20/0.64  thf('87', plain,
% 0.20/0.64      ((((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['81', '86'])).
% 0.20/0.64  thf('88', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.64  thf('89', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('90', plain,
% 0.20/0.64      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['88', '89'])).
% 0.20/0.64  thf('91', plain,
% 0.20/0.64      (![X16 : $i, X17 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.64          | ((X16) != (k1_xboole_0))
% 0.20/0.64          | (v2_compts_1 @ X16 @ X17)
% 0.20/0.64          | ~ (v1_compts_1 @ (k1_pre_topc @ X17 @ X16))
% 0.20/0.64          | ~ (l1_pre_topc @ X17))),
% 0.20/0.64      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.64  thf('92', plain,
% 0.20/0.64      (![X17 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X17)
% 0.20/0.64          | ~ (v1_compts_1 @ (k1_pre_topc @ X17 @ k1_xboole_0))
% 0.20/0.64          | (v2_compts_1 @ k1_xboole_0 @ X17)
% 0.20/0.64          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.64  thf('93', plain,
% 0.20/0.64      ((((v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['90', '92'])).
% 0.20/0.64  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('95', plain,
% 0.20/0.64      ((((v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.64  thf('96', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.64  thf('97', plain,
% 0.20/0.64      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf('98', plain,
% 0.20/0.64      ((~ (v2_compts_1 @ k1_xboole_0 @ sk_A))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['96', '97'])).
% 0.20/0.64  thf('99', plain,
% 0.20/0.64      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('clc', [status(thm)], ['95', '98'])).
% 0.20/0.64  thf('100', plain,
% 0.20/0.64      ((~ (l1_pre_topc @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('clc', [status(thm)], ['87', '99'])).
% 0.20/0.64  thf('101', plain,
% 0.20/0.64      ((~ (l1_pre_topc @ sk_A))
% 0.20/0.64         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['6', '100'])).
% 0.20/0.64  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('103', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.20/0.64       ~
% 0.20/0.64       ((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.64       ~
% 0.20/0.64       ((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['101', '102'])).
% 0.20/0.64  thf('104', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('105', plain,
% 0.20/0.64      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf('106', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.64       ~
% 0.20/0.64       ((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['104', '105'])).
% 0.20/0.64  thf('107', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | (l1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.64  thf('108', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 0.20/0.64      inference('split', [status(esa)], ['0'])).
% 0.20/0.64  thf('109', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('110', plain,
% 0.20/0.64      (![X16 : $i, X17 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.64          | ~ (v2_pre_topc @ X17)
% 0.20/0.64          | ((X16) = (k1_xboole_0))
% 0.20/0.64          | (v1_compts_1 @ (k1_pre_topc @ X17 @ X16))
% 0.20/0.64          | ~ (v2_compts_1 @ X16 @ X17)
% 0.20/0.64          | ~ (l1_pre_topc @ X17))),
% 0.20/0.64      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.64  thf('111', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.64         | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ~ (v2_pre_topc @ sk_A)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['109', '110'])).
% 0.20/0.64  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('113', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('114', plain,
% 0.20/0.64      (((~ (v2_compts_1 @ sk_B @ sk_A)
% 0.20/0.64         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.20/0.64  thf('115', plain,
% 0.20/0.64      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['108', '114'])).
% 0.20/0.64  thf('116', plain,
% 0.20/0.64      (![X8 : $i]:
% 0.20/0.64         ((v2_pre_topc @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ X8) @ (u1_pre_topc @ X8)))
% 0.20/0.64          | ~ (l1_pre_topc @ X8)
% 0.20/0.64          | ~ (v2_pre_topc @ X8))),
% 0.20/0.64      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.20/0.64  thf('117', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X0)
% 0.20/0.64          | (l1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.64  thf('118', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['10'])).
% 0.20/0.64  thf('119', plain,
% 0.20/0.64      (![X16 : $i, X17 : $i]:
% 0.20/0.64         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.20/0.64          | ~ (v2_pre_topc @ X17)
% 0.20/0.64          | ((X16) = (k1_xboole_0))
% 0.20/0.64          | (v2_compts_1 @ X16 @ X17)
% 0.20/0.64          | ~ (v1_compts_1 @ (k1_pre_topc @ X17 @ X16))
% 0.20/0.64          | ~ (l1_pre_topc @ X17))),
% 0.20/0.64      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.20/0.64  thf('120', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v1_compts_1 @ 
% 0.20/0.64              (k1_pre_topc @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64               sk_B))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ~ (v2_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['118', '119'])).
% 0.20/0.64  thf('121', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['38', '47', '52'])).
% 0.20/0.64  thf('122', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ~ (v2_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['120', '121'])).
% 0.20/0.64  thf('123', plain,
% 0.20/0.64      (((~ (l1_pre_topc @ sk_A)
% 0.20/0.64         | ~ (v2_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['117', '122'])).
% 0.20/0.64  thf('124', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('125', plain,
% 0.20/0.64      (((~ (v2_pre_topc @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['123', '124'])).
% 0.20/0.64  thf('126', plain,
% 0.20/0.64      (((~ (v2_pre_topc @ sk_A)
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.64         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['116', '125'])).
% 0.20/0.64  thf('127', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('129', plain,
% 0.20/0.64      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['126', '127', '128'])).
% 0.20/0.64  thf('130', plain,
% 0.20/0.64      (((((sk_B) = (k1_xboole_0))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))
% 0.20/0.64         | (v2_compts_1 @ sk_B @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['115', '129'])).
% 0.20/0.64  thf('131', plain,
% 0.20/0.64      ((((v2_compts_1 @ sk_B @ 
% 0.20/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ((sk_B) = (k1_xboole_0))))
% 0.20/0.64         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['130'])).
% 0.20/0.64  thf('132', plain,
% 0.20/0.64      ((~ (v2_compts_1 @ sk_B @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf('133', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.64  thf('134', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['10'])).
% 0.20/0.64  thf('135', plain,
% 0.20/0.64      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['133', '134'])).
% 0.20/0.64  thf('136', plain,
% 0.20/0.64      (![X17 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X17)
% 0.20/0.64          | ~ (v1_compts_1 @ (k1_pre_topc @ X17 @ k1_xboole_0))
% 0.20/0.64          | (v2_compts_1 @ k1_xboole_0 @ X17)
% 0.20/0.64          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['91'])).
% 0.20/0.64  thf('137', plain,
% 0.20/0.64      ((((v2_compts_1 @ k1_xboole_0 @ 
% 0.20/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (v1_compts_1 @ 
% 0.20/0.64              (k1_pre_topc @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64               k1_xboole_0))
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['135', '136'])).
% 0.20/0.64  thf('138', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.64  thf('139', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['38', '47', '52'])).
% 0.20/0.64  thf('140', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64             k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['138', '139'])).
% 0.20/0.64  thf('141', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.64  thf('142', plain,
% 0.20/0.64      ((((k1_pre_topc @ sk_A @ k1_xboole_0)
% 0.20/0.64          = (k1_pre_topc @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.20/0.64             k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['140', '141'])).
% 0.20/0.64  thf('143', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.64  thf('144', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.64  thf('145', plain,
% 0.20/0.64      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['143', '144'])).
% 0.20/0.64  thf('146', plain,
% 0.20/0.64      (![X17 : $i]:
% 0.20/0.64         (~ (l1_pre_topc @ X17)
% 0.20/0.64          | ~ (v2_compts_1 @ k1_xboole_0 @ X17)
% 0.20/0.64          | (v1_compts_1 @ (k1_pre_topc @ X17 @ k1_xboole_0))
% 0.20/0.64          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.20/0.64      inference('simplify', [status(thm)], ['75'])).
% 0.20/0.64  thf('147', plain,
% 0.20/0.64      ((((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.20/0.64         | ~ (v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['145', '146'])).
% 0.20/0.64  thf('148', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.64  thf('149', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 0.20/0.64      inference('split', [status(esa)], ['0'])).
% 0.20/0.64  thf('150', plain,
% 0.20/0.64      (((v2_compts_1 @ k1_xboole_0 @ sk_A))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup+', [status(thm)], ['148', '149'])).
% 0.20/0.64  thf('151', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('152', plain,
% 0.20/0.64      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['147', '150', '151'])).
% 0.20/0.64  thf('153', plain,
% 0.20/0.64      ((((v2_compts_1 @ k1_xboole_0 @ 
% 0.20/0.64          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64         | ~ (l1_pre_topc @ 
% 0.20/0.64              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['137', '142', '152'])).
% 0.20/0.64  thf('154', plain,
% 0.20/0.64      ((((sk_B) = (k1_xboole_0)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['131', '132'])).
% 0.20/0.64  thf('155', plain,
% 0.20/0.64      ((~ (v2_compts_1 @ sk_B @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf('156', plain,
% 0.20/0.64      ((~ (v2_compts_1 @ k1_xboole_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['154', '155'])).
% 0.20/0.64  thf('157', plain,
% 0.20/0.64      ((~ (l1_pre_topc @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('clc', [status(thm)], ['153', '156'])).
% 0.20/0.64  thf('158', plain,
% 0.20/0.64      ((~ (l1_pre_topc @ sk_A))
% 0.20/0.64         <= (~
% 0.20/0.64             ((v2_compts_1 @ sk_B @ 
% 0.20/0.64               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.20/0.64             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['107', '157'])).
% 0.20/0.64  thf('159', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('160', plain,
% 0.20/0.64      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.20/0.64       ((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.20/0.64       ~
% 0.20/0.64       ((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['158', '159'])).
% 0.20/0.64  thf('161', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.20/0.64        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('162', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.64       ((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.20/0.64      inference('split', [status(esa)], ['161'])).
% 0.20/0.64  thf('163', plain,
% 0.20/0.64      (((v2_compts_1 @ sk_B @ 
% 0.20/0.64         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.20/0.64        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('164', plain,
% 0.20/0.64      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.20/0.64      inference('split', [status(esa)], ['163'])).
% 0.20/0.64  thf('165', plain,
% 0.20/0.64      (![X0 : $i]:
% 0.20/0.64         (((u1_struct_0 @ 
% 0.20/0.64            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.20/0.64            = (u1_struct_0 @ X0))
% 0.20/0.64          | ~ (l1_pre_topc @ X0))),
% 0.20/0.64      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.64  thf('166', plain,
% 0.20/0.64      ((~ (m1_subset_1 @ sk_B @ 
% 0.20/0.64           (k1_zfmisc_1 @ 
% 0.20/0.64            (u1_struct_0 @ 
% 0.20/0.64             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('split', [status(esa)], ['2'])).
% 0.20/0.64  thf('167', plain,
% 0.20/0.64      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.64         | ~ (l1_pre_topc @ sk_A)))
% 0.20/0.64         <= (~
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['165', '166'])).
% 0.20/0.64  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.64  thf('169', plain,
% 0.20/0.64      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.64         <= (~
% 0.20/0.64             ((m1_subset_1 @ sk_B @ 
% 0.20/0.64               (k1_zfmisc_1 @ 
% 0.20/0.64                (u1_struct_0 @ 
% 0.20/0.64                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.20/0.64      inference('demod', [status(thm)], ['167', '168'])).
% 0.20/0.64  thf('170', plain,
% 0.20/0.64      (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.20/0.64       ((m1_subset_1 @ sk_B @ 
% 0.20/0.64         (k1_zfmisc_1 @ 
% 0.20/0.64          (u1_struct_0 @ 
% 0.20/0.64           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.20/0.64      inference('sup-', [status(thm)], ['164', '169'])).
% 0.20/0.64  thf('171', plain, ($false),
% 0.20/0.64      inference('sat_resolution*', [status(thm)],
% 0.20/0.64                ['1', '3', '103', '106', '160', '162', '170'])).
% 0.20/0.64  
% 0.20/0.64  % SZS output end Refutation
% 0.20/0.64  
% 0.20/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
