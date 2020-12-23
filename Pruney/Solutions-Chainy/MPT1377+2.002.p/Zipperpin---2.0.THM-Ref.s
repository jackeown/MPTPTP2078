%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CYjFddGsop

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  218 (6479 expanded)
%              Number of leaves         :   28 (1868 expanded)
%              Depth                    :   34
%              Number of atoms          : 3427 (102450 expanded)
%              Number of equality atoms :   84 (2638 expanded)
%              Maximal formula depth    :   13 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(dt_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) )
        & ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( l1_pre_topc @ ( g1_pre_topc @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
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
    ! [X11: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
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
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( X18 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('13',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('20',plain,(
    ! [X10: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( g1_pre_topc @ X14 @ X15 )
       != ( g1_pre_topc @ X12 @ X13 ) )
      | ( X14 = X12 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( X3
       != ( k1_pre_topc @ X2 @ X1 ) )
      | ( ( k2_struct_0 @ X3 )
        = X1 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X2 @ X1 ) @ X2 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
        = sk_B )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
        = sk_B )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('39',plain,
    ( ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('44',plain,
    ( ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['36','41','46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( ( k2_struct_0 @ X3 )
       != X1 )
      | ( X3
        = ( k1_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( X3
        = ( k1_pre_topc @ X2 @ ( k2_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( ( k1_pre_topc @ sk_A @ sk_B )
          = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
        | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
        | ~ ( l1_pre_topc @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['36','41','46'])).

thf('52',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( ( k1_pre_topc @ sk_A @ sk_B )
          = ( k1_pre_topc @ X0 @ sk_B ) )
        | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ X0 )
        | ~ ( l1_pre_topc @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( k1_pre_topc @ sk_A @ sk_B )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','53'])).

thf('55',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('56',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('57',plain,
    ( ( ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ~ ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('62',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','64'])).

thf('66',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( ( k1_pre_topc @ sk_A @ sk_B )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['54','65'])).

thf('67',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_pre_topc @ sk_A @ sk_B )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','69'])).

thf('71',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','70'])).

thf('72',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('80',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( X18 = k1_xboole_0 )
      | ( v2_compts_1 @ X18 @ X19 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('81',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['78','84'])).

thf('86',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('90',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18 != k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('92',plain,(
    ! [X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X19 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','92'])).

thf('94',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('95',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('96',plain,
    ( ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['93','96'])).

thf('98',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('99',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('100',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('102',plain,
    ( ( ( k1_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('105',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('106',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18 != k1_xboole_0 )
      | ( v2_compts_1 @ X18 @ X19 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('108',plain,(
    ! [X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X19 @ k1_xboole_0 ) )
      | ( v2_compts_1 @ k1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('113',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('114',plain,
    ( ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['111','114'])).

thf('116',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['103','115'])).

thf('117',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','116'])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('121',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('122',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('124',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('125',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('126',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( X18 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( v2_compts_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('127',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['124','130'])).

thf('132',plain,(
    ! [X11: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X11 ) @ ( u1_pre_topc @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( v2_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('134',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('135',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_pre_topc @ X19 )
      | ( X18 = k1_xboole_0 )
      | ( v2_compts_1 @ X18 @ X19 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X19 @ X18 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('136',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('138',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['133','138'])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['132','141'])).

thf('143',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['131','145'])).

thf('147',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('149',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('151',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('153',plain,
    ( ( ( k1_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('155',plain,(
    ! [X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X19 @ k1_xboole_0 ) )
      | ( v2_compts_1 @ k1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('159',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('160',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X19: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X19 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X19 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('162',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('164',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('165',plain,
    ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['162','165','166'])).

thf('168',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('170',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['157','167','168','169'])).

thf('171',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('172',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('173',plain,
    ( ~ ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['170','173'])).

thf('175',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['123','174'])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['178'])).

thf('180',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('183',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('184',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['181','186'])).

thf('188',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','119','122','177','179','187'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CYjFddGsop
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:23:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 310 iterations in 0.125s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.57  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.57  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.57  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.21/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.57  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.21/0.57  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 0.21/0.57  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.57  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.57  thf(t33_compts_1, conjecture,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( ( v2_compts_1 @ B @ A ) & 
% 0.21/0.57             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.21/0.57           ( ( v2_compts_1 @
% 0.21/0.57               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.21/0.57             ( m1_subset_1 @
% 0.21/0.57               B @ 
% 0.21/0.57               ( k1_zfmisc_1 @
% 0.21/0.57                 ( u1_struct_0 @
% 0.21/0.57                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i]:
% 0.21/0.57        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.57            ( l1_pre_topc @ A ) ) =>
% 0.21/0.57          ( ![B:$i]:
% 0.21/0.57            ( ( ( v2_compts_1 @ B @ A ) & 
% 0.21/0.57                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 0.21/0.57              ( ( v2_compts_1 @
% 0.21/0.57                  B @ 
% 0.21/0.57                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.21/0.57                ( m1_subset_1 @
% 0.21/0.57                  B @ 
% 0.21/0.57                  ( k1_zfmisc_1 @
% 0.21/0.57                    ( u1_struct_0 @
% 0.21/0.57                      ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t33_compts_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57        | (v2_compts_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       ((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      ((~ (m1_subset_1 @ sk_B @ 
% 0.21/0.57           (k1_zfmisc_1 @ 
% 0.21/0.57            (u1_struct_0 @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57        | ~ (v2_compts_1 @ sk_B @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       ~
% 0.21/0.57       ((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.21/0.57       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ~
% 0.21/0.57       ((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf(dt_u1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( m1_subset_1 @
% 0.21/0.57         ( u1_pre_topc @ A ) @ 
% 0.21/0.57         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X10 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.57  thf(dt_g1_pre_topc, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 0.21/0.57         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         ((l1_pre_topc @ (g1_pre_topc @ X4 @ X5))
% 0.21/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (l1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (l1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf(fc6_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.57       ( ( v1_pre_topc @
% 0.21/0.57           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 0.21/0.57         ( v2_pre_topc @
% 0.21/0.57           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X11 : $i]:
% 0.21/0.57         ((v2_pre_topc @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.57          | ~ (l1_pre_topc @ X11)
% 0.21/0.57          | ~ (v2_pre_topc @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57        | (v2_compts_1 @ sk_B @ sk_A))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('split', [status(esa)], ['10'])).
% 0.21/0.57  thf(t12_compts_1, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.57               ( ( v2_compts_1 @ B @ A ) <=>
% 0.21/0.57                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 0.21/0.57             ( ( v2_pre_topc @ A ) =>
% 0.21/0.57               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.57                 ( ( v2_compts_1 @ B @ A ) <=>
% 0.21/0.57                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (v2_pre_topc @ X19)
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.21/0.57          | ~ (v2_compts_1 @ X18 @ X19)
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (v2_compts_1 @ sk_B @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | (v1_compts_1 @ 
% 0.21/0.57            (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ~ (v2_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (l1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('split', [status(esa)], ['10'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (![X10 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i]:
% 0.21/0.57         ((v1_pre_topc @ (g1_pre_topc @ X4 @ X5))
% 0.21/0.57          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.57  thf(abstractness_v1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ( v1_pre_topc @ A ) =>
% 0.21/0.57         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (v1_pre_topc @ X0)
% 0.21/0.57          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (![X10 : $i]:
% 0.21/0.57         ((m1_subset_1 @ (u1_pre_topc @ X10) @ 
% 0.21/0.57           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10))))
% 0.21/0.57          | ~ (l1_pre_topc @ X10))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 0.21/0.57  thf(free_g1_pre_topc, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.57       ( ![C:$i,D:$i]:
% 0.21/0.57         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 0.21/0.57           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.57         (((g1_pre_topc @ X14 @ X15) != (g1_pre_topc @ X12 @ X13))
% 0.21/0.57          | ((X14) = (X12))
% 0.21/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X14))))),
% 0.21/0.57      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ((u1_struct_0 @ X0) = (X1))
% 0.21/0.57          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 0.21/0.57              != (g1_pre_topc @ X1 @ X2)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (((X0) != (g1_pre_topc @ X2 @ X1))
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (v1_pre_topc @ X0)
% 0.21/0.57          | ((u1_struct_0 @ X0) = (X2))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('sup-', [status(thm)], ['19', '22'])).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i]:
% 0.21/0.57         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 0.21/0.57          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 0.21/0.57          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | ~ (l1_pre_topc @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57          | ((u1_struct_0 @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57              = (u1_struct_0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (l1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((u1_struct_0 @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57            = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('split', [status(esa)], ['10'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.57  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf(d10_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.57           ( ![C:$i]:
% 0.21/0.57             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.57               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.21/0.57                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.57          | ((X3) != (k1_pre_topc @ X2 @ X1))
% 0.21/0.57          | ((k2_struct_0 @ X3) = (X1))
% 0.21/0.57          | ~ (m1_pre_topc @ X3 @ X2)
% 0.21/0.57          | ~ (v1_pre_topc @ X3)
% 0.21/0.57          | ~ (l1_pre_topc @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X2)
% 0.21/0.57          | ~ (v1_pre_topc @ (k1_pre_topc @ X2 @ X1))
% 0.21/0.57          | ~ (m1_pre_topc @ (k1_pre_topc @ X2 @ X1) @ X2)
% 0.21/0.57          | ((k2_struct_0 @ (k1_pre_topc @ X2 @ X1)) = (X1))
% 0.21/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.21/0.57         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57         | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['31', '33'])).
% 0.21/0.57  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.21/0.57         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57         | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf(dt_k1_pre_topc, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( ( l1_pre_topc @ A ) & 
% 0.21/0.57         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.57       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.21/0.57         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X6)
% 0.21/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.57          | (m1_pre_topc @ (k1_pre_topc @ X6 @ X7) @ X6))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      ((((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.57  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X6 : $i, X7 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X6)
% 0.21/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 0.21/0.57          | (v1_pre_topc @ (k1_pre_topc @ X6 @ X7)))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.57  thf('45', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['36', '41', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.21/0.57          | ((k2_struct_0 @ X3) != (X1))
% 0.21/0.57          | ((X3) = (k1_pre_topc @ X2 @ X1))
% 0.21/0.57          | ~ (m1_pre_topc @ X3 @ X2)
% 0.21/0.57          | ~ (v1_pre_topc @ X3)
% 0.21/0.57          | ~ (l1_pre_topc @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X2 : $i, X3 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X2)
% 0.21/0.57          | ~ (v1_pre_topc @ X3)
% 0.21/0.57          | ~ (m1_pre_topc @ X3 @ X2)
% 0.21/0.57          | ((X3) = (k1_pre_topc @ X2 @ (k2_struct_0 @ X3)))
% 0.21/0.57          | ~ (m1_subset_1 @ (k2_struct_0 @ X3) @ 
% 0.21/0.57               (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.57           | ((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57               = (k1_pre_topc @ X0 @ 
% 0.21/0.57                  (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57           | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.57           | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57           | ~ (l1_pre_topc @ X0)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['47', '49'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['36', '41', '46'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.57           | ((k1_pre_topc @ sk_A @ sk_B) = (k1_pre_topc @ X0 @ sk_B))
% 0.21/0.57           | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ X0)
% 0.21/0.57           | ~ (l1_pre_topc @ X0)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57             = (k1_pre_topc @ 
% 0.21/0.57                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57                sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['15', '53'])).
% 0.21/0.57  thf('55', plain,
% 0.21/0.57      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf(t65_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]:
% 0.21/0.57         ( ( l1_pre_topc @ B ) =>
% 0.21/0.57           ( ( m1_pre_topc @ A @ B ) <=>
% 0.21/0.57             ( m1_pre_topc @
% 0.21/0.57               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.21/0.57  thf('56', plain,
% 0.21/0.57      (![X16 : $i, X17 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X16)
% 0.21/0.57          | ~ (m1_pre_topc @ X17 @ X16)
% 0.21/0.57          | (m1_pre_topc @ X17 @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.21/0.57          | ~ (l1_pre_topc @ X17))),
% 0.21/0.57      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.21/0.57  thf('57', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.57  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('59', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.57  thf('60', plain,
% 0.21/0.57      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf(dt_m1_pre_topc, axiom,
% 0.21/0.57    (![A:$i]:
% 0.21/0.57     ( ( l1_pre_topc @ A ) =>
% 0.21/0.57       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.57  thf('61', plain,
% 0.21/0.57      (![X8 : $i, X9 : $i]:
% 0.21/0.57         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.21/0.57      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.57  thf('62', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['60', '61'])).
% 0.21/0.57  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('64', plain,
% 0.21/0.57      (((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.57  thf('65', plain,
% 0.21/0.57      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['59', '64'])).
% 0.21/0.57  thf('66', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57             = (k1_pre_topc @ 
% 0.21/0.57                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57                sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['54', '65'])).
% 0.21/0.57  thf('67', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57             = (k1_pre_topc @ 
% 0.21/0.57                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57                sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['14', '66'])).
% 0.21/0.57  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('69', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.57  thf('70', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (v2_compts_1 @ sk_B @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ~ (v2_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['13', '69'])).
% 0.21/0.57  thf('71', plain,
% 0.21/0.57      (((~ (v2_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ~ (l1_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '70'])).
% 0.21/0.57  thf('72', plain,
% 0.21/0.57      (((~ (v2_pre_topc @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '71'])).
% 0.21/0.57  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('75', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.21/0.57  thf('76', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '75'])).
% 0.21/0.57  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('78', plain,
% 0.21/0.57      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['76', '77'])).
% 0.21/0.57  thf('79', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('80', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (v2_pre_topc @ X19)
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | (v2_compts_1 @ X18 @ X19)
% 0.21/0.57          | ~ (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.21/0.57  thf('81', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ sk_A)
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ~ (v2_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.21/0.57  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('84', plain,
% 0.21/0.57      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ sk_A)
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.21/0.57  thf('85', plain,
% 0.21/0.57      (((((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ sk_A)))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['78', '84'])).
% 0.21/0.57  thf('86', plain,
% 0.21/0.57      ((((v2_compts_1 @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['85'])).
% 0.21/0.57  thf('87', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('88', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('89', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('split', [status(esa)], ['10'])).
% 0.21/0.57  thf('90', plain,
% 0.21/0.57      (((m1_subset_1 @ k1_xboole_0 @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['88', '89'])).
% 0.21/0.57  thf('91', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ((X18) != (k1_xboole_0))
% 0.21/0.57          | (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.21/0.57          | ~ (v2_compts_1 @ X18 @ X19)
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.21/0.57  thf('92', plain,
% 0.21/0.57      (![X19 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X19)
% 0.21/0.57          | ~ (v2_compts_1 @ k1_xboole_0 @ X19)
% 0.21/0.57          | (v1_compts_1 @ (k1_pre_topc @ X19 @ k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['91'])).
% 0.21/0.57  thf('93', plain,
% 0.21/0.57      ((((v1_compts_1 @ 
% 0.21/0.57          (k1_pre_topc @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57           k1_xboole_0))
% 0.21/0.57         | ~ (v2_compts_1 @ k1_xboole_0 @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (l1_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['90', '92'])).
% 0.21/0.57  thf('94', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('95', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('96', plain,
% 0.21/0.57      (((v2_compts_1 @ k1_xboole_0 @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['94', '95'])).
% 0.21/0.57  thf('97', plain,
% 0.21/0.57      ((((v1_compts_1 @ 
% 0.21/0.57          (k1_pre_topc @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57           k1_xboole_0))
% 0.21/0.57         | ~ (l1_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['93', '96'])).
% 0.21/0.57  thf('98', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('99', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.57  thf('100', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57             k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['98', '99'])).
% 0.21/0.57  thf('101', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('102', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ k1_xboole_0)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57             k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['100', '101'])).
% 0.21/0.57  thf('103', plain,
% 0.21/0.57      ((((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.21/0.57         | ~ (l1_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['97', '102'])).
% 0.21/0.57  thf('104', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('105', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('106', plain,
% 0.21/0.57      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['104', '105'])).
% 0.21/0.57  thf('107', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ((X18) != (k1_xboole_0))
% 0.21/0.57          | (v2_compts_1 @ X18 @ X19)
% 0.21/0.57          | ~ (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.21/0.57  thf('108', plain,
% 0.21/0.57      (![X19 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X19)
% 0.21/0.57          | ~ (v1_compts_1 @ (k1_pre_topc @ X19 @ k1_xboole_0))
% 0.21/0.57          | (v2_compts_1 @ k1_xboole_0 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['107'])).
% 0.21/0.57  thf('109', plain,
% 0.21/0.57      ((((v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['106', '108'])).
% 0.21/0.57  thf('110', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('111', plain,
% 0.21/0.57      ((((v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['109', '110'])).
% 0.21/0.57  thf('112', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['86', '87'])).
% 0.21/0.57  thf('113', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('114', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ k1_xboole_0 @ sk_A))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['112', '113'])).
% 0.21/0.57  thf('115', plain,
% 0.21/0.57      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('clc', [status(thm)], ['111', '114'])).
% 0.21/0.57  thf('116', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('clc', [status(thm)], ['103', '115'])).
% 0.21/0.57  thf('117', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.57         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['6', '116'])).
% 0.21/0.57  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('119', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       ~
% 0.21/0.57       ((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.21/0.57       ~
% 0.21/0.57       ((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['117', '118'])).
% 0.21/0.57  thf('120', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('121', plain,
% 0.21/0.57      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('122', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ~
% 0.21/0.57       ((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['120', '121'])).
% 0.21/0.57  thf('123', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (l1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('124', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('125', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('126', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (v2_pre_topc @ X19)
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.21/0.57          | ~ (v2_compts_1 @ X18 @ X19)
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.21/0.57  thf('127', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v2_compts_1 @ sk_B @ sk_A)
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ~ (v2_pre_topc @ sk_A)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['125', '126'])).
% 0.21/0.57  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('130', plain,
% 0.21/0.57      (((~ (v2_compts_1 @ sk_B @ sk_A)
% 0.21/0.57         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.21/0.57  thf('131', plain,
% 0.21/0.57      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['124', '130'])).
% 0.21/0.57  thf('132', plain,
% 0.21/0.57      (![X11 : $i]:
% 0.21/0.57         ((v2_pre_topc @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ X11) @ (u1_pre_topc @ X11)))
% 0.21/0.57          | ~ (l1_pre_topc @ X11)
% 0.21/0.57          | ~ (v2_pre_topc @ X11))),
% 0.21/0.57      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 0.21/0.57  thf('133', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X0)
% 0.21/0.57          | (l1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.57  thf('134', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('split', [status(esa)], ['10'])).
% 0.21/0.57  thf('135', plain,
% 0.21/0.57      (![X18 : $i, X19 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.57          | ~ (v2_pre_topc @ X19)
% 0.21/0.57          | ((X18) = (k1_xboole_0))
% 0.21/0.57          | (v2_compts_1 @ X18 @ X19)
% 0.21/0.57          | ~ (v1_compts_1 @ (k1_pre_topc @ X19 @ X18))
% 0.21/0.57          | ~ (l1_pre_topc @ X19))),
% 0.21/0.57      inference('cnf', [status(esa)], [t12_compts_1])).
% 0.21/0.57  thf('136', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (v1_compts_1 @ 
% 0.21/0.57              (k1_pre_topc @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57               sk_B))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ~ (v2_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['134', '135'])).
% 0.21/0.57  thf('137', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.57  thf('138', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ~ (v2_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['136', '137'])).
% 0.21/0.57  thf('139', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v2_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['133', '138'])).
% 0.21/0.57  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('141', plain,
% 0.21/0.57      (((~ (v2_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['139', '140'])).
% 0.21/0.57  thf('142', plain,
% 0.21/0.57      (((~ (v2_pre_topc @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['132', '141'])).
% 0.21/0.57  thf('143', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('144', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('145', plain,
% 0.21/0.57      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.21/0.57  thf('146', plain,
% 0.21/0.57      (((((sk_B) = (k1_xboole_0))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))
% 0.21/0.57         | (v2_compts_1 @ sk_B @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['131', '145'])).
% 0.21/0.57  thf('147', plain,
% 0.21/0.57      ((((v2_compts_1 @ sk_B @ 
% 0.21/0.57          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ((sk_B) = (k1_xboole_0))))
% 0.21/0.57         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['146'])).
% 0.21/0.57  thf('148', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_B @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('149', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.57  thf('150', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['67', '68'])).
% 0.21/0.57  thf('151', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ sk_B)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57             k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['149', '150'])).
% 0.21/0.57  thf('152', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.57  thf('153', plain,
% 0.21/0.57      ((((k1_pre_topc @ sk_A @ k1_xboole_0)
% 0.21/0.57          = (k1_pre_topc @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 0.21/0.57             k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['151', '152'])).
% 0.21/0.57  thf('154', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((u1_struct_0 @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57            = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('155', plain,
% 0.21/0.57      (![X19 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X19)
% 0.21/0.57          | ~ (v1_compts_1 @ (k1_pre_topc @ X19 @ k1_xboole_0))
% 0.21/0.57          | (v2_compts_1 @ k1_xboole_0 @ X19)
% 0.21/0.57          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['107'])).
% 0.21/0.57  thf('156', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.21/0.57          | ~ (l1_pre_topc @ X0)
% 0.21/0.57          | (v2_compts_1 @ k1_xboole_0 @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57          | ~ (v1_compts_1 @ 
% 0.21/0.57               (k1_pre_topc @ 
% 0.21/0.57                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 0.21/0.57                k1_xboole_0))
% 0.21/0.57          | ~ (l1_pre_topc @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['154', '155'])).
% 0.21/0.57  thf('157', plain,
% 0.21/0.57      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.21/0.57         | ~ (l1_pre_topc @ 
% 0.21/0.57              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | (v2_compts_1 @ k1_xboole_0 @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)
% 0.21/0.57         | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['153', '156'])).
% 0.21/0.57  thf('158', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.57  thf('159', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.57  thf('160', plain,
% 0.21/0.57      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['158', '159'])).
% 0.21/0.57  thf('161', plain,
% 0.21/0.57      (![X19 : $i]:
% 0.21/0.57         (~ (l1_pre_topc @ X19)
% 0.21/0.57          | ~ (v2_compts_1 @ k1_xboole_0 @ X19)
% 0.21/0.57          | (v1_compts_1 @ (k1_pre_topc @ X19 @ k1_xboole_0))
% 0.21/0.57          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['91'])).
% 0.21/0.57  thf('162', plain,
% 0.21/0.57      ((((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 0.21/0.57         | ~ (v2_compts_1 @ k1_xboole_0 @ sk_A)
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['160', '161'])).
% 0.21/0.57  thf('163', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.57  thf('164', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('165', plain,
% 0.21/0.57      (((v2_compts_1 @ k1_xboole_0 @ sk_A))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['163', '164'])).
% 0.21/0.57  thf('166', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('167', plain,
% 0.21/0.57      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['162', '165', '166'])).
% 0.21/0.57  thf('168', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('169', plain,
% 0.21/0.57      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup+', [status(thm)], ['158', '159'])).
% 0.21/0.57  thf('170', plain,
% 0.21/0.57      (((~ (l1_pre_topc @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57         | (v2_compts_1 @ k1_xboole_0 @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['157', '167', '168', '169'])).
% 0.21/0.57  thf('171', plain,
% 0.21/0.57      ((((sk_B) = (k1_xboole_0)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['147', '148'])).
% 0.21/0.57  thf('172', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ sk_B @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('173', plain,
% 0.21/0.57      ((~ (v2_compts_1 @ k1_xboole_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['171', '172'])).
% 0.21/0.57  thf('174', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('clc', [status(thm)], ['170', '173'])).
% 0.21/0.57  thf('175', plain,
% 0.21/0.57      ((~ (l1_pre_topc @ sk_A))
% 0.21/0.57         <= (~
% 0.21/0.57             ((v2_compts_1 @ sk_B @ 
% 0.21/0.57               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 0.21/0.57             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['123', '174'])).
% 0.21/0.57  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('177', plain,
% 0.21/0.57      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 0.21/0.57       ((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 0.21/0.57       ~
% 0.21/0.57       ((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['175', '176'])).
% 0.21/0.57  thf('178', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 0.21/0.57        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('179', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.21/0.57      inference('split', [status(esa)], ['178'])).
% 0.21/0.57  thf('180', plain,
% 0.21/0.57      (((v2_compts_1 @ sk_B @ 
% 0.21/0.57         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.21/0.57        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('181', plain,
% 0.21/0.57      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.57      inference('split', [status(esa)], ['180'])).
% 0.21/0.57  thf('182', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((u1_struct_0 @ 
% 0.21/0.57            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.21/0.57            = (u1_struct_0 @ X0))
% 0.21/0.57          | ~ (l1_pre_topc @ X0))),
% 0.21/0.57      inference('clc', [status(thm)], ['25', '26'])).
% 0.21/0.57  thf('183', plain,
% 0.21/0.57      ((~ (m1_subset_1 @ sk_B @ 
% 0.21/0.57           (k1_zfmisc_1 @ 
% 0.21/0.57            (u1_struct_0 @ 
% 0.21/0.57             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('split', [status(esa)], ['2'])).
% 0.21/0.57  thf('184', plain,
% 0.21/0.57      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.57         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['182', '183'])).
% 0.21/0.57  thf('185', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('186', plain,
% 0.21/0.57      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.57         <= (~
% 0.21/0.57             ((m1_subset_1 @ sk_B @ 
% 0.21/0.57               (k1_zfmisc_1 @ 
% 0.21/0.57                (u1_struct_0 @ 
% 0.21/0.57                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 0.21/0.57      inference('demod', [status(thm)], ['184', '185'])).
% 0.21/0.57  thf('187', plain,
% 0.21/0.57      (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.57       ((m1_subset_1 @ sk_B @ 
% 0.21/0.57         (k1_zfmisc_1 @ 
% 0.21/0.57          (u1_struct_0 @ 
% 0.21/0.57           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['181', '186'])).
% 0.21/0.57  thf('188', plain, ($false),
% 0.21/0.57      inference('sat_resolution*', [status(thm)],
% 0.21/0.57                ['1', '3', '119', '122', '177', '179', '187'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
