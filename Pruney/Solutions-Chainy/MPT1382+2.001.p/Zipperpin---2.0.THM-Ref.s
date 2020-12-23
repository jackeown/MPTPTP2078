%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5oJ8LQPk4x

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:49 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 229 expanded)
%              Number of leaves         :   24 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :  847 (3948 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t7_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( m1_connsp_2 @ C @ A @ B )
                  & ! [D: $i] :
                      ( ( ~ ( v1_xboole_0 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                     => ~ ( ( m1_connsp_2 @ D @ A @ B )
                          & ( v3_pre_topc @ D @ A )
                          & ( r1_tarski @ D @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( m1_connsp_2 @ C @ A @ B )
                    & ! [D: $i] :
                        ( ( ~ ( v1_xboole_0 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ B )
                            & ( v3_pre_topc @ D @ A )
                            & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_connsp_2])).

thf('0',plain,(
    m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_connsp_2 @ sk_C_1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X23 @ X22 ) @ X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('24',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X37: $i] :
      ( ~ ( r1_tarski @ X37 @ sk_C_1 )
      | ~ ( v3_pre_topc @ X37 @ sk_A )
      | ~ ( m1_connsp_2 @ X37 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t55_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('38',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) )
   <= ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
   <= ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ! [X26: $i,X27: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
        | ~ ( l1_pre_topc @ X27 )
        | ~ ( v2_pre_topc @ X27 )
        | ( ( k1_tops_1 @ X27 @ X26 )
         != X26 )
        | ( v3_pre_topc @ X26 @ X27 ) )
    | ! [X24: $i,X25: $i] :
        ( ~ ( l1_pre_topc @ X24 )
        | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) ) ) ),
    inference(split,[status(esa)],['37'])).

thf('45',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference('sat_resolution*',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( ( k1_tops_1 @ X27 @ X26 )
       != X26 )
      | ( v3_pre_topc @ X26 @ X27 ) ) ),
    inference(simpl_trail,[status(thm)],['38','45'])).

thf('47',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
     != ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ ( k1_tops_1 @ X20 @ X21 ) )
        = ( k1_tops_1 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      = ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C_1 )
     != ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['47','52','53','54'])).

thf('56',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['35','56'])).

thf('58',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('59',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('60',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X29 ) )
      | ~ ( r2_hidden @ X28 @ ( k1_tops_1 @ X29 @ X30 ) )
      | ( m1_connsp_2 @ X30 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    = ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_connsp_2 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A @ sk_B ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    v1_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['57','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['18','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5oJ8LQPk4x
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 155 iterations in 0.100s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.19/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.55  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.19/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(t7_connsp_2, conjecture,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55               ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.19/0.55                    ( ![D:$i]:
% 0.19/0.55                      ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.19/0.55                          ( m1_subset_1 @
% 0.19/0.55                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.55                        ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.19/0.55                             ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i]:
% 0.19/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.55            ( l1_pre_topc @ A ) ) =>
% 0.19/0.55          ( ![B:$i]:
% 0.19/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.55              ( ![C:$i]:
% 0.19/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55                  ( ~( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.19/0.55                       ( ![D:$i]:
% 0.19/0.55                         ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.19/0.55                             ( m1_subset_1 @
% 0.19/0.55                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.55                           ( ~( ( m1_connsp_2 @ D @ A @ B ) & 
% 0.19/0.55                                ( v3_pre_topc @ D @ A ) & ( r1_tarski @ D @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t7_connsp_2])).
% 0.19/0.55  thf('0', plain, ((m1_connsp_2 @ sk_C_1 @ sk_A @ sk_B)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(d1_connsp_2, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.19/0.55                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.19/0.55          | ~ (m1_connsp_2 @ X30 @ X29 @ X28)
% 0.19/0.55          | (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 0.19/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.19/0.55          | ~ (l1_pre_topc @ X29)
% 0.19/0.55          | ~ (v2_pre_topc @ X29)
% 0.19/0.55          | (v2_struct_0 @ X29))),
% 0.19/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.55  thf('4', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55          | ~ (m1_connsp_2 @ sk_C_1 @ sk_A @ X0)
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.55        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55        | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['0', '6'])).
% 0.19/0.55  thf('8', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)) | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.55  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('11', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.55      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf(d10_xboole_0, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.55  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.55  thf(t3_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X11 : $i, X13 : $i]:
% 0.19/0.55         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('15', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.55  thf(t5_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.19/0.55          ( v1_xboole_0 @ C ) ) ))).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X17 @ X18)
% 0.19/0.55          | ~ (v1_xboole_0 @ X19)
% 0.19/0.55          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t5_subset])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.55  thf('18', plain, (~ (v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['11', '17'])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (![X11 : $i, X12 : $i]:
% 0.19/0.55         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('21', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t44_tops_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( l1_pre_topc @ A ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (![X22 : $i, X23 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.19/0.55          | (r1_tarski @ (k1_tops_1 @ X23 @ X22) @ X22)
% 0.19/0.55          | ~ (l1_pre_topc @ X23))),
% 0.19/0.55      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.19/0.55        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.55  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('26', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.19/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.55  thf(t1_xboole_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.55       ( r1_tarski @ A @ C ) ))).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X3 @ X4)
% 0.19/0.55          | ~ (r1_tarski @ X4 @ X5)
% 0.19/0.55          | (r1_tarski @ X3 @ X5))),
% 0.19/0.55      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ X0)
% 0.19/0.55          | ~ (r1_tarski @ sk_C_1 @ X0))),
% 0.19/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['21', '28'])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (![X11 : $i, X13 : $i]:
% 0.19/0.55         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.19/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      (![X37 : $i]:
% 0.19/0.55         (~ (r1_tarski @ X37 @ sk_C_1)
% 0.19/0.55          | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.19/0.55          | ~ (m1_connsp_2 @ X37 @ sk_A @ sk_B)
% 0.19/0.55          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.55          | (v1_xboole_0 @ X37))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.55        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.19/0.55        | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.55  thf('34', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.19/0.55      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.55        | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.19/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.55  thf(t55_tops_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.55       ( ![B:$i]:
% 0.19/0.55         ( ( l1_pre_topc @ B ) =>
% 0.19/0.55           ( ![C:$i]:
% 0.19/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.55               ( ![D:$i]:
% 0.19/0.55                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.19/0.55                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.19/0.55                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.19/0.55                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.19/0.55                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X24)
% 0.19/0.55          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.19/0.55          | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.19/0.55          | (v3_pre_topc @ X26 @ X27)
% 0.19/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.55          | ~ (l1_pre_topc @ X27)
% 0.19/0.55          | ~ (v2_pre_topc @ X27))),
% 0.19/0.55      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      ((![X26 : $i, X27 : $i]:
% 0.19/0.55          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.55           | ~ (l1_pre_topc @ X27)
% 0.19/0.55           | ~ (v2_pre_topc @ X27)
% 0.19/0.55           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.19/0.55           | (v3_pre_topc @ X26 @ X27)))
% 0.19/0.55         <= ((![X26 : $i, X27 : $i]:
% 0.19/0.55                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.55                 | ~ (l1_pre_topc @ X27)
% 0.19/0.55                 | ~ (v2_pre_topc @ X27)
% 0.19/0.55                 | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.19/0.55                 | (v3_pre_topc @ X26 @ X27))))),
% 0.19/0.55      inference('split', [status(esa)], ['37'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      ((![X24 : $i, X25 : $i]:
% 0.19/0.55          (~ (l1_pre_topc @ X24)
% 0.19/0.55           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))
% 0.19/0.55         <= ((![X24 : $i, X25 : $i]:
% 0.19/0.55                (~ (l1_pre_topc @ X24)
% 0.19/0.55                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))))),
% 0.19/0.55      inference('split', [status(esa)], ['37'])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      ((~ (l1_pre_topc @ sk_A))
% 0.19/0.55         <= ((![X24 : $i, X25 : $i]:
% 0.19/0.55                (~ (l1_pre_topc @ X24)
% 0.19/0.55                 | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24))))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.55  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('43', plain,
% 0.19/0.55      (~
% 0.19/0.55       (![X24 : $i, X25 : $i]:
% 0.19/0.55          (~ (l1_pre_topc @ X24)
% 0.19/0.55           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))),
% 0.19/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.19/0.55  thf('44', plain,
% 0.19/0.55      ((![X26 : $i, X27 : $i]:
% 0.19/0.55          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.55           | ~ (l1_pre_topc @ X27)
% 0.19/0.55           | ~ (v2_pre_topc @ X27)
% 0.19/0.55           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.19/0.55           | (v3_pre_topc @ X26 @ X27))) | 
% 0.19/0.55       (![X24 : $i, X25 : $i]:
% 0.19/0.55          (~ (l1_pre_topc @ X24)
% 0.19/0.55           | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))))),
% 0.19/0.55      inference('split', [status(esa)], ['37'])).
% 0.19/0.55  thf('45', plain,
% 0.19/0.55      ((![X26 : $i, X27 : $i]:
% 0.19/0.55          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.55           | ~ (l1_pre_topc @ X27)
% 0.19/0.55           | ~ (v2_pre_topc @ X27)
% 0.19/0.55           | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.19/0.55           | (v3_pre_topc @ X26 @ X27)))),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['43', '44'])).
% 0.19/0.55  thf('46', plain,
% 0.19/0.55      (![X26 : $i, X27 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.19/0.55          | ~ (l1_pre_topc @ X27)
% 0.19/0.55          | ~ (v2_pre_topc @ X27)
% 0.19/0.55          | ((k1_tops_1 @ X27 @ X26) != (X26))
% 0.19/0.55          | (v3_pre_topc @ X26 @ X27))),
% 0.19/0.55      inference('simpl_trail', [status(thm)], ['38', '45'])).
% 0.19/0.55  thf('47', plain,
% 0.19/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.19/0.55        | ((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55            != (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['36', '46'])).
% 0.19/0.55  thf('48', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(projectivity_k1_tops_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( l1_pre_topc @ A ) & 
% 0.19/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.55       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.19/0.55  thf('49', plain,
% 0.19/0.55      (![X20 : $i, X21 : $i]:
% 0.19/0.55         (~ (l1_pre_topc @ X20)
% 0.19/0.55          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.55          | ((k1_tops_1 @ X20 @ (k1_tops_1 @ X20 @ X21))
% 0.19/0.55              = (k1_tops_1 @ X20 @ X21)))),
% 0.19/0.55      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.19/0.55  thf('50', plain,
% 0.19/0.55      ((((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55          = (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.55  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('52', plain,
% 0.19/0.55      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55         = (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.55  thf('53', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('55', plain,
% 0.19/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.19/0.55        | ((k1_tops_1 @ sk_A @ sk_C_1) != (k1_tops_1 @ sk_A @ sk_C_1)))),
% 0.19/0.55      inference('demod', [status(thm)], ['47', '52', '53', '54'])).
% 0.19/0.55  thf('56', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 0.19/0.55      inference('simplify', [status(thm)], ['55'])).
% 0.19/0.55  thf('57', plain,
% 0.19/0.55      (((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55        | ~ (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['35', '56'])).
% 0.19/0.55  thf('58', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.55      inference('clc', [status(thm)], ['9', '10'])).
% 0.19/0.55  thf('59', plain,
% 0.19/0.55      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 0.19/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.55  thf('60', plain,
% 0.19/0.55      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.19/0.55         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X29))
% 0.19/0.55          | ~ (r2_hidden @ X28 @ (k1_tops_1 @ X29 @ X30))
% 0.19/0.55          | (m1_connsp_2 @ X30 @ X29 @ X28)
% 0.19/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.19/0.55          | ~ (l1_pre_topc @ X29)
% 0.19/0.55          | ~ (v2_pre_topc @ X29)
% 0.19/0.55          | (v2_struct_0 @ X29))),
% 0.19/0.55      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.19/0.55  thf('61', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.55          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.55          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.19/0.55          | ~ (r2_hidden @ X0 @ 
% 0.19/0.55               (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.55  thf('62', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('64', plain,
% 0.19/0.55      (((k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55         = (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.55  thf('65', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((v2_struct_0 @ sk_A)
% 0.19/0.55          | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ X0)
% 0.19/0.55          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 0.19/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.55      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 0.19/0.55  thf('66', plain,
% 0.19/0.55      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.19/0.55        | (m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.55        | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('sup-', [status(thm)], ['58', '65'])).
% 0.19/0.55  thf('67', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('68', plain,
% 0.19/0.55      (((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)
% 0.19/0.55        | (v2_struct_0 @ sk_A))),
% 0.19/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.19/0.55  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('70', plain, ((m1_connsp_2 @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A @ sk_B)),
% 0.19/0.55      inference('clc', [status(thm)], ['68', '69'])).
% 0.19/0.55  thf('71', plain, ((v1_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 0.19/0.55      inference('demod', [status(thm)], ['57', '70'])).
% 0.19/0.55  thf('72', plain, ($false), inference('demod', [status(thm)], ['18', '71'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
