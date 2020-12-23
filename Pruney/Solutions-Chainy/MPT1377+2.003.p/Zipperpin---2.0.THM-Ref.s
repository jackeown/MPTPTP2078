%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xw5z3tpcpf

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:44 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  253 (14080 expanded)
%              Number of leaves         :   29 (3996 expanded)
%              Depth                    :   39
%              Number of atoms          : 4264 (237621 expanded)
%              Number of equality atoms :  112 (6180 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_compts_1_type,type,(
    v2_compts_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(v1_compts_1_type,type,(
    v1_compts_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
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
    ! [X9: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_pre_topc @ X22 )
      | ( X21 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( v2_compts_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('13',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
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

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( X18 != X20 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ X19 @ X18 ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ X19 @ X18 ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t66_pre_topc])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ X19 @ X20 ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ X19 @ X20 ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X19 ) @ ( u1_pre_topc @ X19 ) ) @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
        = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( v1_pre_topc @ ( g1_pre_topc @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_g1_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(abstractness_v1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( v1_pre_topc @ A )
       => ( A
          = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_pre_topc @ X0 )
      | ( X0
        = ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_pre_topc])).

thf('24',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( u1_pre_topc @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_pre_topc])).

thf(free_g1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_pre_topc @ A @ B )
            = ( g1_pre_topc @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( ( g1_pre_topc @ X12 @ X13 )
       != ( g1_pre_topc @ X10 @ X11 ) )
      | ( X12 = X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_pre_topc])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) )
       != ( g1_pre_topc @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X2 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ X2 @ X1 ) )
        = X2 )
      | ~ ( v1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('33',plain,
    ( ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X15 @ X14 ) )
        = X14 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('38',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('45',plain,
    ( ( ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','35','40'])).

thf('47',plain,
    ( ( ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('51',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ ( g1_pre_topc @ ( u1_struct_0 @ X17 ) @ ( u1_pre_topc @ X17 ) ) )
      | ( m1_pre_topc @ X16 @ X17 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('52',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ sk_A )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

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

thf('57',plain,(
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

thf('58',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X2 @ X1 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X2 @ X1 ) @ X2 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X2 @ X1 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( ( k2_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
        = sk_B )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('62',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( l1_pre_topc @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('63',plain,
    ( ( ( v1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( ( k2_struct_0 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
        = sk_B )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['59','66'])).

thf('68',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','35','40'])).

thf('69',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','35','40'])).

thf('70',plain,
    ( ( ( ( k2_struct_0 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
        = sk_B )
      | ~ ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('72',plain,
    ( ( ( ( k2_struct_0 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
        = sk_B )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_struct_0 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
        = sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','72'])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_struct_0 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
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

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( l1_pre_topc @ X2 )
      | ~ ( v1_pre_topc @ X3 )
      | ~ ( m1_pre_topc @ X3 @ X2 )
      | ( X3
        = ( k1_pre_topc @ X2 @ ( k2_struct_0 @ X3 ) ) )
      | ~ ( m1_subset_1 @ ( k2_struct_0 @ X3 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
          = ( k1_pre_topc @ X0 @ ( k2_struct_0 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ) ) )
        | ~ ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ X0 )
        | ~ ( v1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
        | ~ ( l1_pre_topc @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( ( k2_struct_0 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      = sk_B )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('80',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('81',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','35','40'])).

thf('82',plain,
    ( ( v1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
        | ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
          = ( k1_pre_topc @ X0 @ sk_B ) )
        | ~ ( m1_pre_topc @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) @ X0 )
        | ~ ( l1_pre_topc @ X0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['78','79','82'])).

thf('84',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
        = ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['54','83'])).

thf('85',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('87',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','87'])).

thf('89',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['13','88'])).

thf('90',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['9','89'])).

thf('91',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','90'])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['7','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('99',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_pre_topc @ X22 )
      | ( X21 = k1_xboole_0 )
      | ( v2_compts_1 @ X21 @ X22 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('100',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ sk_A ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,
    ( ( ( v2_compts_1 @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('107',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('109',plain,
    ( ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('111',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( X21 != k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( v2_compts_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('112',plain,(
    ! [X22: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X22 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X22 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 ) )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['109','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('117',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('118',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','118'])).

thf('120',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('121',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','87'])).

thf('122',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('124',plain,
    ( ( ( k1_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['119','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('127',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( X21 != k1_xboole_0 )
      | ( v2_compts_1 @ X21 @ X22 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('128',plain,(
    ! [X22: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X22 @ k1_xboole_0 ) )
      | ( v2_compts_1 @ k1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('133',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
   <= ~ ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('134',plain,
    ( ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['131','134'])).

thf('136',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['125','135'])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      & ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['6','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
    | ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('143',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('144',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['141','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('149',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['140'])).

thf('151',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_pre_topc @ X22 )
      | ( X21 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( v2_compts_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('152',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['149','155'])).

thf('157',plain,(
    ! [X9: $i] :
      ( ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X9 ) @ ( u1_pre_topc @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_pre_topc])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('159',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(split,[status(esa)],['10'])).

thf('160',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_pre_topc @ X22 )
      | ( X21 = k1_xboole_0 )
      | ( v2_compts_1 @ X21 @ X22 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('161',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['19','35','40'])).

thf('163',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( g1_pre_topc @ sk_B @ ( u1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
      = ( k1_pre_topc @ sk_A @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('165',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['158','165'])).

thf('167',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ~ ( v2_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['157','168'])).

thf('170',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','172'])).

thf('174',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('176',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ sk_B ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['41','87'])).

thf('178',plain,
    ( ( ( k1_pre_topc @ sk_A @ sk_B )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('180',plain,
    ( ( ( k1_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('182',plain,(
    ! [X22: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ X22 @ k1_xboole_0 ) )
      | ( v2_compts_1 @ k1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( v1_compts_1 @ ( k1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['180','183'])).

thf('185',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('186',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('187',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_pre_topc @ X22 )
      | ( X21 = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X22 @ X21 ) )
      | ~ ( v2_compts_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_compts_1])).

thf('188',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ~ ( v2_compts_1 @ sk_B @ sk_A )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['188','189','190'])).

thf('192',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['185','191'])).

thf('193',plain,
    ( ( ~ ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('194',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,
    ( ( ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['194'])).

thf('196',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('197',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('199',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X22: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ X22 )
      | ( v1_compts_1 @ ( k1_pre_topc @ X22 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('201',plain,
    ( ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
      | ~ ( v2_compts_1 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('203',plain,
    ( ( v2_compts_1 @ sk_B @ sk_A )
   <= ( v2_compts_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('204',plain,
    ( ( v2_compts_1 @ k1_xboole_0 @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['202','203'])).

thf('205',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,
    ( ( v1_compts_1 @ ( k1_pre_topc @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['201','204','205'])).

thf('207',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['197','198'])).

thf('209',plain,
    ( ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['184','206','207','208'])).

thf('210',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('211',plain,
    ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('212',plain,
    ( ~ ( v2_compts_1 @ k1_xboole_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( l1_pre_topc @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['209','212'])).

thf('214',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ( ~ ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      & ( v2_compts_1 @ sk_B @ sk_A )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      & ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['148','213'])).

thf('215',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ~ ( v2_compts_1 @ sk_B @ sk_A )
    | ( v2_compts_1 @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['214','215'])).

thf('217',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['217'])).

thf('219',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('220',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('221',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ) ) )
    | ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','139','147','216','218','221'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Xw5z3tpcpf
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.01/1.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.01/1.21  % Solved by: fo/fo7.sh
% 1.01/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.21  % done 1200 iterations in 0.756s
% 1.01/1.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.01/1.21  % SZS output start Refutation
% 1.01/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.21  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.01/1.21  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 1.01/1.21  thf(v2_compts_1_type, type, v2_compts_1: $i > $i > $o).
% 1.01/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.21  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 1.01/1.21  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.01/1.21  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 1.01/1.21  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 1.01/1.21  thf(v1_compts_1_type, type, v1_compts_1: $i > $o).
% 1.01/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.01/1.21  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.21  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 1.01/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.01/1.21  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.01/1.21  thf(t33_compts_1, conjecture,
% 1.01/1.21    (![A:$i]:
% 1.01/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.21       ( ![B:$i]:
% 1.01/1.21         ( ( ( v2_compts_1 @ B @ A ) & 
% 1.01/1.21             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 1.01/1.21           ( ( v2_compts_1 @
% 1.01/1.21               B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.01/1.21             ( m1_subset_1 @
% 1.01/1.21               B @ 
% 1.01/1.21               ( k1_zfmisc_1 @
% 1.01/1.21                 ( u1_struct_0 @
% 1.01/1.21                   ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ))).
% 1.01/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.21    (~( ![A:$i]:
% 1.01/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.01/1.21            ( l1_pre_topc @ A ) ) =>
% 1.01/1.21          ( ![B:$i]:
% 1.01/1.21            ( ( ( v2_compts_1 @ B @ A ) & 
% 1.01/1.21                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) <=>
% 1.01/1.21              ( ( v2_compts_1 @
% 1.01/1.21                  B @ 
% 1.01/1.22                  ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.01/1.22                ( m1_subset_1 @
% 1.01/1.22                  B @ 
% 1.01/1.22                  ( k1_zfmisc_1 @
% 1.01/1.22                    ( u1_struct_0 @
% 1.01/1.22                      ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) ) ) ) ) )),
% 1.01/1.22    inference('cnf.neg', [status(esa)], [t33_compts_1])).
% 1.01/1.22  thf('0', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('1', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 1.01/1.22       ((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))),
% 1.01/1.22      inference('split', [status(esa)], ['0'])).
% 1.01/1.22  thf('2', plain,
% 1.01/1.22      ((~ (m1_subset_1 @ sk_B @ 
% 1.01/1.22           (k1_zfmisc_1 @ 
% 1.01/1.22            (u1_struct_0 @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22        | ~ (v2_compts_1 @ sk_B @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.22        | ~ (v2_compts_1 @ sk_B @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('3', plain,
% 1.01/1.22      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 1.01/1.22       ~
% 1.01/1.22       ((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 1.01/1.22       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.01/1.22       ~
% 1.01/1.22       ((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf(dt_u1_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( m1_subset_1 @
% 1.01/1.22         ( u1_pre_topc @ A ) @ 
% 1.01/1.22         ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ))).
% 1.01/1.22  thf('4', plain,
% 1.01/1.22      (![X8 : $i]:
% 1.01/1.22         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 1.01/1.22           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 1.01/1.22          | ~ (l1_pre_topc @ X8))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.01/1.22  thf(dt_g1_pre_topc, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.22       ( ( v1_pre_topc @ ( g1_pre_topc @ A @ B ) ) & 
% 1.01/1.22         ( l1_pre_topc @ ( g1_pre_topc @ A @ B ) ) ) ))).
% 1.01/1.22  thf('5', plain,
% 1.01/1.22      (![X4 : $i, X5 : $i]:
% 1.01/1.22         ((l1_pre_topc @ (g1_pre_topc @ X4 @ X5))
% 1.01/1.22          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 1.01/1.22  thf('6', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('7', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf(fc6_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.01/1.22       ( ( v1_pre_topc @
% 1.01/1.22           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) & 
% 1.01/1.22         ( v2_pre_topc @
% 1.01/1.22           ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.01/1.22  thf('8', plain,
% 1.01/1.22      (![X9 : $i]:
% 1.01/1.22         ((v2_pre_topc @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 1.01/1.22          | ~ (l1_pre_topc @ X9)
% 1.01/1.22          | ~ (v2_pre_topc @ X9))),
% 1.01/1.22      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 1.01/1.22  thf('9', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['0'])).
% 1.01/1.22  thf('10', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22        | (v2_compts_1 @ sk_B @ sk_A))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('11', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf(t12_compts_1, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.22           ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.01/1.22               ( ( v2_compts_1 @ B @ A ) <=>
% 1.01/1.22                 ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) & 
% 1.01/1.22             ( ( v2_pre_topc @ A ) =>
% 1.01/1.22               ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 1.01/1.22                 ( ( v2_compts_1 @ B @ A ) <=>
% 1.01/1.22                   ( v1_compts_1 @ ( k1_pre_topc @ A @ B ) ) ) ) ) ) ) ) ))).
% 1.01/1.22  thf('12', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ~ (v2_pre_topc @ X22)
% 1.01/1.22          | ((X21) = (k1_xboole_0))
% 1.01/1.22          | (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('13', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v2_compts_1 @ sk_B @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ 
% 1.01/1.22            (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['11', '12'])).
% 1.01/1.22  thf('14', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf(t66_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.22           ( ![C:$i]:
% 1.01/1.22             ( ( m1_subset_1 @
% 1.01/1.22                 C @ 
% 1.01/1.22                 ( k1_zfmisc_1 @
% 1.01/1.22                   ( u1_struct_0 @
% 1.01/1.22                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ) =>
% 1.01/1.22               ( ( ( B ) = ( C ) ) =>
% 1.01/1.22                 ( ( g1_pre_topc @
% 1.01/1.22                     ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) @ 
% 1.01/1.22                     ( u1_pre_topc @ ( k1_pre_topc @ A @ B ) ) ) =
% 1.01/1.22                   ( k1_pre_topc @
% 1.01/1.22                     ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) @ 
% 1.01/1.22                     C ) ) ) ) ) ) ) ))).
% 1.01/1.22  thf('15', plain,
% 1.01/1.22      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.01/1.22          | ((X18) != (X20))
% 1.01/1.22          | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ X19 @ X18)) @ 
% 1.01/1.22              (u1_pre_topc @ (k1_pre_topc @ X19 @ X18)))
% 1.01/1.22              = (k1_pre_topc @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)) @ 
% 1.01/1.22                 X20))
% 1.01/1.22          | ~ (m1_subset_1 @ X20 @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))))
% 1.01/1.22          | ~ (l1_pre_topc @ X19))),
% 1.01/1.22      inference('cnf', [status(esa)], [t66_pre_topc])).
% 1.01/1.22  thf('16', plain,
% 1.01/1.22      (![X19 : $i, X20 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X19)
% 1.01/1.22          | ~ (m1_subset_1 @ X20 @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)))))
% 1.01/1.22          | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ X19 @ X20)) @ 
% 1.01/1.22              (u1_pre_topc @ (k1_pre_topc @ X19 @ X20)))
% 1.01/1.22              = (k1_pre_topc @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ X19) @ (u1_pre_topc @ X19)) @ 
% 1.01/1.22                 X20))
% 1.01/1.22          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['15'])).
% 1.01/1.22  thf('17', plain,
% 1.01/1.22      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.22         | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.01/1.22             (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22             = (k1_pre_topc @ 
% 1.01/1.22                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22                sk_B))
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['14', '16'])).
% 1.01/1.22  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('19', plain,
% 1.01/1.22      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.22         | ((g1_pre_topc @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ 
% 1.01/1.22             (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22             = (k1_pre_topc @ 
% 1.01/1.22                (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22                sk_B))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['17', '18'])).
% 1.01/1.22  thf('20', plain,
% 1.01/1.22      (![X8 : $i]:
% 1.01/1.22         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 1.01/1.22           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 1.01/1.22          | ~ (l1_pre_topc @ X8))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.01/1.22  thf('21', plain,
% 1.01/1.22      (![X4 : $i, X5 : $i]:
% 1.01/1.22         ((v1_pre_topc @ (g1_pre_topc @ X4 @ X5))
% 1.01/1.22          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_g1_pre_topc])).
% 1.01/1.22  thf('22', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (v1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['20', '21'])).
% 1.01/1.22  thf(abstractness_v1_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( ( v1_pre_topc @ A ) =>
% 1.01/1.22         ( ( A ) = ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) ) ))).
% 1.01/1.22  thf('23', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (v1_pre_topc @ X0)
% 1.01/1.22          | ((X0) = (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22          | ~ (l1_pre_topc @ X0))),
% 1.01/1.22      inference('cnf', [status(esa)], [abstractness_v1_pre_topc])).
% 1.01/1.22  thf('24', plain,
% 1.01/1.22      (![X8 : $i]:
% 1.01/1.22         ((m1_subset_1 @ (u1_pre_topc @ X8) @ 
% 1.01/1.22           (k1_zfmisc_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8))))
% 1.01/1.22          | ~ (l1_pre_topc @ X8))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_u1_pre_topc])).
% 1.01/1.22  thf(free_g1_pre_topc, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.22       ( ![C:$i,D:$i]:
% 1.01/1.22         ( ( ( g1_pre_topc @ A @ B ) = ( g1_pre_topc @ C @ D ) ) =>
% 1.01/1.22           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 1.01/1.22  thf('25', plain,
% 1.01/1.22      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.01/1.22         (((g1_pre_topc @ X12 @ X13) != (g1_pre_topc @ X10 @ X11))
% 1.01/1.22          | ((X12) = (X10))
% 1.01/1.22          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 1.01/1.22      inference('cnf', [status(esa)], [free_g1_pre_topc])).
% 1.01/1.22  thf('26', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | ((u1_struct_0 @ X0) = (X1))
% 1.01/1.22          | ((g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))
% 1.01/1.22              != (g1_pre_topc @ X1 @ X2)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['24', '25'])).
% 1.01/1.22  thf('27', plain,
% 1.01/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.22         (((X0) != (g1_pre_topc @ X2 @ X1))
% 1.01/1.22          | ~ (l1_pre_topc @ X0)
% 1.01/1.22          | ~ (v1_pre_topc @ X0)
% 1.01/1.22          | ((u1_struct_0 @ X0) = (X2))
% 1.01/1.22          | ~ (l1_pre_topc @ X0))),
% 1.01/1.22      inference('sup-', [status(thm)], ['23', '26'])).
% 1.01/1.22  thf('28', plain,
% 1.01/1.22      (![X1 : $i, X2 : $i]:
% 1.01/1.22         (((u1_struct_0 @ (g1_pre_topc @ X2 @ X1)) = (X2))
% 1.01/1.22          | ~ (v1_pre_topc @ (g1_pre_topc @ X2 @ X1))
% 1.01/1.22          | ~ (l1_pre_topc @ (g1_pre_topc @ X2 @ X1)))),
% 1.01/1.22      inference('simplify', [status(thm)], ['27'])).
% 1.01/1.22  thf('29', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | ~ (l1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22          | ((u1_struct_0 @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22              = (u1_struct_0 @ X0)))),
% 1.01/1.22      inference('sup-', [status(thm)], ['22', '28'])).
% 1.01/1.22  thf('30', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('31', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((u1_struct_0 @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22            = (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (l1_pre_topc @ X0))),
% 1.01/1.22      inference('clc', [status(thm)], ['29', '30'])).
% 1.01/1.22  thf('32', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf('33', plain,
% 1.01/1.22      ((((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['31', '32'])).
% 1.01/1.22  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('35', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('36', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf(t29_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.22           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 1.01/1.22  thf('37', plain,
% 1.01/1.22      (![X14 : $i, X15 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.01/1.22          | ((u1_struct_0 @ (k1_pre_topc @ X15 @ X14)) = (X14))
% 1.01/1.22          | ~ (l1_pre_topc @ X15))),
% 1.01/1.22      inference('cnf', [status(esa)], [t29_pre_topc])).
% 1.01/1.22  thf('38', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['36', '37'])).
% 1.01/1.22  thf('39', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('40', plain,
% 1.01/1.22      ((((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['38', '39'])).
% 1.01/1.22  thf('41', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '35', '40'])).
% 1.01/1.22  thf('42', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('43', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf(dt_k1_pre_topc, axiom,
% 1.01/1.22    (![A:$i,B:$i]:
% 1.01/1.22     ( ( ( l1_pre_topc @ A ) & 
% 1.01/1.22         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.01/1.22       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 1.01/1.22         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 1.01/1.22  thf('44', plain,
% 1.01/1.22      (![X6 : $i, X7 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X6)
% 1.01/1.22          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.01/1.22          | (m1_pre_topc @ (k1_pre_topc @ X6 @ X7) @ X6))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 1.01/1.22  thf('45', plain,
% 1.01/1.22      ((((m1_pre_topc @ 
% 1.01/1.22          (k1_pre_topc @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B) @ 
% 1.01/1.22          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['43', '44'])).
% 1.01/1.22  thf('46', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '35', '40'])).
% 1.01/1.22  thf('47', plain,
% 1.01/1.22      ((((m1_pre_topc @ 
% 1.01/1.22          (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['45', '46'])).
% 1.01/1.22  thf('48', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | (m1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['42', '47'])).
% 1.01/1.22  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('50', plain,
% 1.01/1.22      (((m1_pre_topc @ 
% 1.01/1.22         (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['48', '49'])).
% 1.01/1.22  thf(t59_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( m1_pre_topc @
% 1.01/1.22             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 1.01/1.22           ( m1_pre_topc @ B @ A ) ) ) ))).
% 1.01/1.22  thf('51', plain,
% 1.01/1.22      (![X16 : $i, X17 : $i]:
% 1.01/1.22         (~ (m1_pre_topc @ X16 @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X17) @ (u1_pre_topc @ X17)))
% 1.01/1.22          | (m1_pre_topc @ X16 @ X17)
% 1.01/1.22          | ~ (l1_pre_topc @ X17))),
% 1.01/1.22      inference('cnf', [status(esa)], [t59_pre_topc])).
% 1.01/1.22  thf('52', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | (m1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22            sk_A)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['50', '51'])).
% 1.01/1.22  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('54', plain,
% 1.01/1.22      (((m1_pre_topc @ 
% 1.01/1.22         (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22         sk_A))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['52', '53'])).
% 1.01/1.22  thf('55', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('56', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf(d10_pre_topc, axiom,
% 1.01/1.22    (![A:$i]:
% 1.01/1.22     ( ( l1_pre_topc @ A ) =>
% 1.01/1.22       ( ![B:$i]:
% 1.01/1.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.01/1.22           ( ![C:$i]:
% 1.01/1.22             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 1.01/1.22               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 1.01/1.22                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 1.01/1.22  thf('57', plain,
% 1.01/1.22      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 1.01/1.22          | ((X3) != (k1_pre_topc @ X2 @ X1))
% 1.01/1.22          | ((k2_struct_0 @ X3) = (X1))
% 1.01/1.22          | ~ (m1_pre_topc @ X3 @ X2)
% 1.01/1.22          | ~ (v1_pre_topc @ X3)
% 1.01/1.22          | ~ (l1_pre_topc @ X2))),
% 1.01/1.22      inference('cnf', [status(esa)], [d10_pre_topc])).
% 1.01/1.22  thf('58', plain,
% 1.01/1.22      (![X1 : $i, X2 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X2)
% 1.01/1.22          | ~ (v1_pre_topc @ (k1_pre_topc @ X2 @ X1))
% 1.01/1.22          | ~ (m1_pre_topc @ (k1_pre_topc @ X2 @ X1) @ X2)
% 1.01/1.22          | ((k2_struct_0 @ (k1_pre_topc @ X2 @ X1)) = (X1))
% 1.01/1.22          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['57'])).
% 1.01/1.22  thf('59', plain,
% 1.01/1.22      (((((k2_struct_0 @ 
% 1.01/1.22           (k1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 1.01/1.22           = (sk_B))
% 1.01/1.22         | ~ (m1_pre_topc @ 
% 1.01/1.22              (k1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22               sk_B) @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v1_pre_topc @ 
% 1.01/1.22              (k1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22               sk_B))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['56', '58'])).
% 1.01/1.22  thf('60', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('61', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf('62', plain,
% 1.01/1.22      (![X6 : $i, X7 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X6)
% 1.01/1.22          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.01/1.22          | (v1_pre_topc @ (k1_pre_topc @ X6 @ X7)))),
% 1.01/1.22      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 1.01/1.22  thf('63', plain,
% 1.01/1.22      ((((v1_pre_topc @ 
% 1.01/1.22          (k1_pre_topc @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['61', '62'])).
% 1.01/1.22  thf('64', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | (v1_pre_topc @ 
% 1.01/1.22            (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['60', '63'])).
% 1.01/1.22  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('66', plain,
% 1.01/1.22      (((v1_pre_topc @ 
% 1.01/1.22         (k1_pre_topc @ 
% 1.01/1.22          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['64', '65'])).
% 1.01/1.22  thf('67', plain,
% 1.01/1.22      (((((k2_struct_0 @ 
% 1.01/1.22           (k1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B))
% 1.01/1.22           = (sk_B))
% 1.01/1.22         | ~ (m1_pre_topc @ 
% 1.01/1.22              (k1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22               sk_B) @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['59', '66'])).
% 1.01/1.22  thf('68', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '35', '40'])).
% 1.01/1.22  thf('69', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '35', '40'])).
% 1.01/1.22  thf('70', plain,
% 1.01/1.22      (((((k2_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22           = (sk_B))
% 1.01/1.22         | ~ (m1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['67', '68', '69'])).
% 1.01/1.22  thf('71', plain,
% 1.01/1.22      (((m1_pre_topc @ 
% 1.01/1.22         (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['48', '49'])).
% 1.01/1.22  thf('72', plain,
% 1.01/1.22      (((((k2_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22           = (sk_B))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['70', '71'])).
% 1.01/1.22  thf('73', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ((k2_struct_0 @ 
% 1.01/1.22             (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22             = (sk_B))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['55', '72'])).
% 1.01/1.22  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('75', plain,
% 1.01/1.22      ((((k2_struct_0 @ 
% 1.01/1.22          (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22          = (sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['73', '74'])).
% 1.01/1.22  thf('76', plain,
% 1.01/1.22      (![X1 : $i, X2 : $i, X3 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 1.01/1.22          | ((k2_struct_0 @ X3) != (X1))
% 1.01/1.22          | ((X3) = (k1_pre_topc @ X2 @ X1))
% 1.01/1.22          | ~ (m1_pre_topc @ X3 @ X2)
% 1.01/1.22          | ~ (v1_pre_topc @ X3)
% 1.01/1.22          | ~ (l1_pre_topc @ X2))),
% 1.01/1.22      inference('cnf', [status(esa)], [d10_pre_topc])).
% 1.01/1.22  thf('77', plain,
% 1.01/1.22      (![X2 : $i, X3 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X2)
% 1.01/1.22          | ~ (v1_pre_topc @ X3)
% 1.01/1.22          | ~ (m1_pre_topc @ X3 @ X2)
% 1.01/1.22          | ((X3) = (k1_pre_topc @ X2 @ (k2_struct_0 @ X3)))
% 1.01/1.22          | ~ (m1_subset_1 @ (k2_struct_0 @ X3) @ 
% 1.01/1.22               (k1_zfmisc_1 @ (u1_struct_0 @ X2))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['76'])).
% 1.01/1.22  thf('78', plain,
% 1.01/1.22      ((![X0 : $i]:
% 1.01/1.22          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.01/1.22           | ((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22               = (k1_pre_topc @ X0 @ 
% 1.01/1.22                  (k2_struct_0 @ 
% 1.01/1.22                   (g1_pre_topc @ sk_B @ 
% 1.01/1.22                    (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))))
% 1.01/1.22           | ~ (m1_pre_topc @ 
% 1.01/1.22                (g1_pre_topc @ sk_B @ 
% 1.01/1.22                 (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22                X0)
% 1.01/1.22           | ~ (v1_pre_topc @ 
% 1.01/1.22                (g1_pre_topc @ sk_B @ 
% 1.01/1.22                 (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22           | ~ (l1_pre_topc @ X0)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['75', '77'])).
% 1.01/1.22  thf('79', plain,
% 1.01/1.22      ((((k2_struct_0 @ 
% 1.01/1.22          (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22          = (sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['73', '74'])).
% 1.01/1.22  thf('80', plain,
% 1.01/1.22      (((v1_pre_topc @ 
% 1.01/1.22         (k1_pre_topc @ 
% 1.01/1.22          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['64', '65'])).
% 1.01/1.22  thf('81', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '35', '40'])).
% 1.01/1.22  thf('82', plain,
% 1.01/1.22      (((v1_pre_topc @ 
% 1.01/1.22         (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['80', '81'])).
% 1.01/1.22  thf('83', plain,
% 1.01/1.22      ((![X0 : $i]:
% 1.01/1.22          (~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.01/1.22           | ((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22               = (k1_pre_topc @ X0 @ sk_B))
% 1.01/1.22           | ~ (m1_pre_topc @ 
% 1.01/1.22                (g1_pre_topc @ sk_B @ 
% 1.01/1.22                 (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))) @ 
% 1.01/1.22                X0)
% 1.01/1.22           | ~ (l1_pre_topc @ X0)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['78', '79', '82'])).
% 1.01/1.22  thf('84', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22             = (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['54', '83'])).
% 1.01/1.22  thf('85', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('86', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('87', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.01/1.22  thf('88', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ sk_B)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['41', '87'])).
% 1.01/1.22  thf('89', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v2_compts_1 @ sk_B @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['13', '88'])).
% 1.01/1.22  thf('90', plain,
% 1.01/1.22      (((~ (v2_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['9', '89'])).
% 1.01/1.22  thf('91', plain,
% 1.01/1.22      (((~ (v2_pre_topc @ sk_A)
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['8', '90'])).
% 1.01/1.22  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('94', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['91', '92', '93'])).
% 1.01/1.22  thf('95', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['7', '94'])).
% 1.01/1.22  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('97', plain,
% 1.01/1.22      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['95', '96'])).
% 1.01/1.22  thf('98', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('99', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ~ (v2_pre_topc @ X22)
% 1.01/1.22          | ((X21) = (k1_xboole_0))
% 1.01/1.22          | (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('100', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ sk_A)
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ sk_A)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['98', '99'])).
% 1.01/1.22  thf('101', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('102', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('103', plain,
% 1.01/1.22      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ sk_A)
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.01/1.22  thf('104', plain,
% 1.01/1.22      (((((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ sk_A)))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['97', '103'])).
% 1.01/1.22  thf('105', plain,
% 1.01/1.22      ((((v2_compts_1 @ sk_B @ sk_A) | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['104'])).
% 1.01/1.22  thf('106', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('107', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.22  thf('108', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['0'])).
% 1.01/1.22  thf('109', plain,
% 1.01/1.22      (((v2_compts_1 @ k1_xboole_0 @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['107', '108'])).
% 1.01/1.22  thf('110', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((u1_struct_0 @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22            = (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (l1_pre_topc @ X0))),
% 1.01/1.22      inference('clc', [status(thm)], ['29', '30'])).
% 1.01/1.22  thf('111', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ((X21) != (k1_xboole_0))
% 1.01/1.22          | (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('112', plain,
% 1.01/1.22      (![X22 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X22)
% 1.01/1.22          | ~ (v2_compts_1 @ k1_xboole_0 @ X22)
% 1.01/1.22          | (v1_compts_1 @ (k1_pre_topc @ X22 @ k1_xboole_0))
% 1.01/1.22          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['111'])).
% 1.01/1.22  thf('113', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.01/1.22          | ~ (l1_pre_topc @ X0)
% 1.01/1.22          | (v1_compts_1 @ 
% 1.01/1.22             (k1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 1.01/1.22              k1_xboole_0))
% 1.01/1.22          | ~ (v2_compts_1 @ k1_xboole_0 @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22          | ~ (l1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['110', '112'])).
% 1.01/1.22  thf('114', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ 
% 1.01/1.22            (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22             k1_xboole_0))
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['109', '113'])).
% 1.01/1.22  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('116', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.22  thf('117', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('118', plain,
% 1.01/1.22      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['116', '117'])).
% 1.01/1.22  thf('119', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ 
% 1.01/1.22            (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22             k1_xboole_0))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['114', '115', '118'])).
% 1.01/1.22  thf('120', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.22  thf('121', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ sk_B)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['41', '87'])).
% 1.01/1.22  thf('122', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ sk_B)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22             k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['120', '121'])).
% 1.01/1.22  thf('123', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.22  thf('124', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ k1_xboole_0)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22             k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['122', '123'])).
% 1.01/1.22  thf('125', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['119', '124'])).
% 1.01/1.22  thf('126', plain,
% 1.01/1.22      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['116', '117'])).
% 1.01/1.22  thf('127', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ((X21) != (k1_xboole_0))
% 1.01/1.22          | (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('128', plain,
% 1.01/1.22      (![X22 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X22)
% 1.01/1.22          | ~ (v1_compts_1 @ (k1_pre_topc @ X22 @ k1_xboole_0))
% 1.01/1.22          | (v2_compts_1 @ k1_xboole_0 @ X22)
% 1.01/1.22          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['127'])).
% 1.01/1.22  thf('129', plain,
% 1.01/1.22      ((((v2_compts_1 @ k1_xboole_0 @ sk_A)
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['126', '128'])).
% 1.01/1.22  thf('130', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('131', plain,
% 1.01/1.22      ((((v2_compts_1 @ k1_xboole_0 @ sk_A)
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['129', '130'])).
% 1.01/1.22  thf('132', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['105', '106'])).
% 1.01/1.22  thf('133', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ sk_B @ sk_A)) <= (~ ((v2_compts_1 @ sk_B @ sk_A)))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('134', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ k1_xboole_0 @ sk_A))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['132', '133'])).
% 1.01/1.22  thf('135', plain,
% 1.01/1.22      ((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('clc', [status(thm)], ['131', '134'])).
% 1.01/1.22  thf('136', plain,
% 1.01/1.22      ((~ (l1_pre_topc @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('clc', [status(thm)], ['125', '135'])).
% 1.01/1.22  thf('137', plain,
% 1.01/1.22      ((~ (l1_pre_topc @ sk_A))
% 1.01/1.22         <= (~ ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['6', '136'])).
% 1.01/1.22  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('139', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ sk_A)) | 
% 1.01/1.22       ~
% 1.01/1.22       ((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 1.01/1.22       ~
% 1.01/1.22       ((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['137', '138'])).
% 1.01/1.22  thf('140', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('141', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['140'])).
% 1.01/1.22  thf('142', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((u1_struct_0 @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22            = (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (l1_pre_topc @ X0))),
% 1.01/1.22      inference('clc', [status(thm)], ['29', '30'])).
% 1.01/1.22  thf('143', plain,
% 1.01/1.22      ((~ (m1_subset_1 @ sk_B @ 
% 1.01/1.22           (k1_zfmisc_1 @ 
% 1.01/1.22            (u1_struct_0 @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('144', plain,
% 1.01/1.22      (((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['142', '143'])).
% 1.01/1.22  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('146', plain,
% 1.01/1.22      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['144', '145'])).
% 1.01/1.22  thf('147', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 1.01/1.22       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['141', '146'])).
% 1.01/1.22  thf('148', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('149', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.01/1.22      inference('split', [status(esa)], ['0'])).
% 1.01/1.22  thf('150', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['140'])).
% 1.01/1.22  thf('151', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ~ (v2_pre_topc @ X22)
% 1.01/1.22          | ((X21) = (k1_xboole_0))
% 1.01/1.22          | (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('152', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (v2_compts_1 @ sk_B @ sk_A)
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ sk_A)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['150', '151'])).
% 1.01/1.22  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('154', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('155', plain,
% 1.01/1.22      (((~ (v2_compts_1 @ sk_B @ sk_A)
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.22      inference('demod', [status(thm)], ['152', '153', '154'])).
% 1.01/1.22  thf('156', plain,
% 1.01/1.22      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['149', '155'])).
% 1.01/1.22  thf('157', plain,
% 1.01/1.22      (![X9 : $i]:
% 1.01/1.22         ((v2_pre_topc @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ X9) @ (u1_pre_topc @ X9)))
% 1.01/1.22          | ~ (l1_pre_topc @ X9)
% 1.01/1.22          | ~ (v2_pre_topc @ X9))),
% 1.01/1.22      inference('cnf', [status(esa)], [fc6_pre_topc])).
% 1.01/1.22  thf('158', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X0)
% 1.01/1.22          | (l1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['4', '5'])).
% 1.01/1.22  thf('159', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('split', [status(esa)], ['10'])).
% 1.01/1.22  thf('160', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ~ (v2_pre_topc @ X22)
% 1.01/1.22          | ((X21) = (k1_xboole_0))
% 1.01/1.22          | (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('161', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v1_compts_1 @ 
% 1.01/1.22              (k1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22               sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['159', '160'])).
% 1.01/1.22  thf('162', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['19', '35', '40'])).
% 1.01/1.22  thf('163', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v1_compts_1 @ 
% 1.01/1.22              (g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['161', '162'])).
% 1.01/1.22  thf('164', plain,
% 1.01/1.22      ((((g1_pre_topc @ sk_B @ (u1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22          = (k1_pre_topc @ sk_A @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['84', '85', '86'])).
% 1.01/1.22  thf('165', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['163', '164'])).
% 1.01/1.22  thf('166', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (v2_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['158', '165'])).
% 1.01/1.22  thf('167', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('168', plain,
% 1.01/1.22      (((~ (v2_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['166', '167'])).
% 1.01/1.22  thf('169', plain,
% 1.01/1.22      (((~ (v2_pre_topc @ sk_A)
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['157', '168'])).
% 1.01/1.22  thf('170', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('172', plain,
% 1.01/1.22      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.01/1.22  thf('173', plain,
% 1.01/1.22      (((((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['156', '172'])).
% 1.01/1.22  thf('174', plain,
% 1.01/1.22      ((((v2_compts_1 @ sk_B @ 
% 1.01/1.22          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['173'])).
% 1.01/1.22  thf('175', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ sk_B @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('176', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['174', '175'])).
% 1.01/1.22  thf('177', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ sk_B)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ sk_B)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['41', '87'])).
% 1.01/1.22  thf('178', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ sk_B)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22             k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['176', '177'])).
% 1.01/1.22  thf('179', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['174', '175'])).
% 1.01/1.22  thf('180', plain,
% 1.01/1.22      ((((k1_pre_topc @ sk_A @ k1_xboole_0)
% 1.01/1.22          = (k1_pre_topc @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)) @ 
% 1.01/1.22             k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['178', '179'])).
% 1.01/1.22  thf('181', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (((u1_struct_0 @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22            = (u1_struct_0 @ X0))
% 1.01/1.22          | ~ (l1_pre_topc @ X0))),
% 1.01/1.22      inference('clc', [status(thm)], ['29', '30'])).
% 1.01/1.22  thf('182', plain,
% 1.01/1.22      (![X22 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X22)
% 1.01/1.22          | ~ (v1_compts_1 @ (k1_pre_topc @ X22 @ k1_xboole_0))
% 1.01/1.22          | (v2_compts_1 @ k1_xboole_0 @ X22)
% 1.01/1.22          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['127'])).
% 1.01/1.22  thf('183', plain,
% 1.01/1.22      (![X0 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.01/1.22          | ~ (l1_pre_topc @ X0)
% 1.01/1.22          | (v2_compts_1 @ k1_xboole_0 @ 
% 1.01/1.22             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 1.01/1.22          | ~ (v1_compts_1 @ 
% 1.01/1.22               (k1_pre_topc @ 
% 1.01/1.22                (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)) @ 
% 1.01/1.22                k1_xboole_0))
% 1.01/1.22          | ~ (l1_pre_topc @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['181', '182'])).
% 1.01/1.22  thf('184', plain,
% 1.01/1.22      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 1.01/1.22         | ~ (l1_pre_topc @ 
% 1.01/1.22              (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v2_compts_1 @ k1_xboole_0 @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['180', '183'])).
% 1.01/1.22  thf('185', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.01/1.22      inference('split', [status(esa)], ['0'])).
% 1.01/1.22  thf('186', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('187', plain,
% 1.01/1.22      (![X21 : $i, X22 : $i]:
% 1.01/1.22         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.01/1.22          | ~ (v2_pre_topc @ X22)
% 1.01/1.22          | ((X21) = (k1_xboole_0))
% 1.01/1.22          | (v1_compts_1 @ (k1_pre_topc @ X22 @ X21))
% 1.01/1.22          | ~ (v2_compts_1 @ X21 @ X22)
% 1.01/1.22          | ~ (l1_pre_topc @ X22))),
% 1.01/1.22      inference('cnf', [status(esa)], [t12_compts_1])).
% 1.01/1.22  thf('188', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ sk_A)
% 1.01/1.22         | ~ (v2_compts_1 @ sk_B @ sk_A)
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ~ (v2_pre_topc @ sk_A)))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['186', '187'])).
% 1.01/1.22  thf('189', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('190', plain, ((v2_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('191', plain,
% 1.01/1.22      (((~ (v2_compts_1 @ sk_B @ sk_A)
% 1.01/1.22         | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['188', '189', '190'])).
% 1.01/1.22  thf('192', plain,
% 1.01/1.22      (((((sk_B) = (k1_xboole_0)) | (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['185', '191'])).
% 1.01/1.22  thf('193', plain,
% 1.01/1.22      (((~ (v1_compts_1 @ (k1_pre_topc @ sk_A @ sk_B))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['169', '170', '171'])).
% 1.01/1.22  thf('194', plain,
% 1.01/1.22      (((((sk_B) = (k1_xboole_0))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))
% 1.01/1.22         | (v2_compts_1 @ sk_B @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['192', '193'])).
% 1.01/1.22  thf('195', plain,
% 1.01/1.22      ((((v2_compts_1 @ sk_B @ 
% 1.01/1.22          (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | ((sk_B) = (k1_xboole_0))))
% 1.01/1.22         <= (((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['194'])).
% 1.01/1.22  thf('196', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ sk_B @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('197', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['195', '196'])).
% 1.01/1.22  thf('198', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('199', plain,
% 1.01/1.22      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['197', '198'])).
% 1.01/1.22  thf('200', plain,
% 1.01/1.22      (![X22 : $i]:
% 1.01/1.22         (~ (l1_pre_topc @ X22)
% 1.01/1.22          | ~ (v2_compts_1 @ k1_xboole_0 @ X22)
% 1.01/1.22          | (v1_compts_1 @ (k1_pre_topc @ X22 @ k1_xboole_0))
% 1.01/1.22          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 1.01/1.22      inference('simplify', [status(thm)], ['111'])).
% 1.01/1.22  thf('201', plain,
% 1.01/1.22      ((((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0))
% 1.01/1.22         | ~ (v2_compts_1 @ k1_xboole_0 @ sk_A)
% 1.01/1.22         | ~ (l1_pre_topc @ sk_A)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['199', '200'])).
% 1.01/1.22  thf('202', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['195', '196'])).
% 1.01/1.22  thf('203', plain,
% 1.01/1.22      (((v2_compts_1 @ sk_B @ sk_A)) <= (((v2_compts_1 @ sk_B @ sk_A)))),
% 1.01/1.22      inference('split', [status(esa)], ['0'])).
% 1.01/1.22  thf('204', plain,
% 1.01/1.22      (((v2_compts_1 @ k1_xboole_0 @ sk_A))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['202', '203'])).
% 1.01/1.22  thf('205', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('206', plain,
% 1.01/1.22      (((v1_compts_1 @ (k1_pre_topc @ sk_A @ k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['201', '204', '205'])).
% 1.01/1.22  thf('207', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('208', plain,
% 1.01/1.22      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup+', [status(thm)], ['197', '198'])).
% 1.01/1.22  thf('209', plain,
% 1.01/1.22      (((~ (l1_pre_topc @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 1.01/1.22         | (v2_compts_1 @ k1_xboole_0 @ 
% 1.01/1.22            (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['184', '206', '207', '208'])).
% 1.01/1.22  thf('210', plain,
% 1.01/1.22      ((((sk_B) = (k1_xboole_0)))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['195', '196'])).
% 1.01/1.22  thf('211', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ sk_B @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('212', plain,
% 1.01/1.22      ((~ (v2_compts_1 @ k1_xboole_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['210', '211'])).
% 1.01/1.22  thf('213', plain,
% 1.01/1.22      ((~ (l1_pre_topc @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('clc', [status(thm)], ['209', '212'])).
% 1.01/1.22  thf('214', plain,
% 1.01/1.22      ((~ (l1_pre_topc @ sk_A))
% 1.01/1.22         <= (~
% 1.01/1.22             ((v2_compts_1 @ sk_B @ 
% 1.01/1.22               (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) & 
% 1.01/1.22             ((v2_compts_1 @ sk_B @ sk_A)) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) & 
% 1.01/1.22             ((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['148', '213'])).
% 1.01/1.22  thf('215', plain, ((l1_pre_topc @ sk_A)),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('216', plain,
% 1.01/1.22      (~ ((v2_compts_1 @ sk_B @ sk_A)) | 
% 1.01/1.22       ((v2_compts_1 @ sk_B @ 
% 1.01/1.22         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))) | 
% 1.01/1.22       ~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.01/1.22       ~
% 1.01/1.22       ((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['214', '215'])).
% 1.01/1.22  thf('217', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))
% 1.01/1.22        | (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.22  thf('218', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 1.01/1.22       ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.22      inference('split', [status(esa)], ['217'])).
% 1.01/1.22  thf('219', plain,
% 1.01/1.22      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (((m1_subset_1 @ sk_B @ 
% 1.01/1.22               (k1_zfmisc_1 @ 
% 1.01/1.22                (u1_struct_0 @ 
% 1.01/1.22                 (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))))),
% 1.01/1.22      inference('demod', [status(thm)], ['33', '34'])).
% 1.01/1.22  thf('220', plain,
% 1.01/1.22      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.01/1.22         <= (~ ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.01/1.22      inference('split', [status(esa)], ['2'])).
% 1.01/1.22  thf('221', plain,
% 1.01/1.22      (~
% 1.01/1.22       ((m1_subset_1 @ sk_B @ 
% 1.01/1.22         (k1_zfmisc_1 @ 
% 1.01/1.22          (u1_struct_0 @ 
% 1.01/1.22           (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))))) | 
% 1.01/1.22       ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.01/1.22      inference('sup-', [status(thm)], ['219', '220'])).
% 1.01/1.22  thf('222', plain, ($false),
% 1.01/1.22      inference('sat_resolution*', [status(thm)],
% 1.01/1.22                ['1', '3', '139', '147', '216', '218', '221'])).
% 1.01/1.22  
% 1.01/1.22  % SZS output end Refutation
% 1.01/1.22  
% 1.01/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
