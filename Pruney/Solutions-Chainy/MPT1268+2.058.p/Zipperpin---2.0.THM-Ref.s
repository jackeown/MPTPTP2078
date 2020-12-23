%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L9E1HMwXM3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 981 expanded)
%              Number of leaves         :   27 ( 272 expanded)
%              Depth                    :   22
%              Number of atoms          : 1223 (15114 expanded)
%              Number of equality atoms :   49 ( 577 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t86_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( r1_tarski @ C @ B )
                    & ( v3_pre_topc @ C @ A ) )
                 => ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( r1_tarski @ C @ B )
                      & ( v3_pre_topc @ C @ A ) )
                   => ( C = k1_xboole_0 ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('7',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('16',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['1'])).

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

thf('22',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('23',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) )
   <= ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('26',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ! [X21: $i,X22: $i] :
        ( ~ ( l1_pre_topc @ X21 )
        | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
        | ~ ( v3_pre_topc @ X22 @ X21 )
        | ( ( k1_tops_1 @ X21 @ X22 )
          = X22 ) )
    | ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference(simpl_trail,[status(thm)],['23','32'])).

thf('34',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X27: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X27 @ sk_A )
      | ~ ( r1_tarski @ X27 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['38'])).

thf('54',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['45','46'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('58',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['54','55','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('65',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X27: $i] :
        ( ( X27 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X27 @ sk_A )
        | ~ ( r1_tarski @ X27 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ~ ! [X27: $i] :
          ( ( X27 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X27 @ sk_A )
          | ~ ( r1_tarski @ X27 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['19'])).

thf('74',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['39','72','73'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['39','72','75'])).

thf('77',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['37','74','76'])).

thf('78',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['37','74','76'])).

thf('79',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['37','74','76'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','77','78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['39','72','75'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','82'])).

thf('84',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['70'])).

thf('85',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['70'])).

thf('86',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['39','72','85'])).

thf('87',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['84','86'])).

thf('88',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['38'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tops_1 @ X25 @ X26 )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['39','72'])).

thf('96',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['83','87','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('100',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('102',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('103',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['106'])).

thf('108',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['106'])).

thf('109',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','72','108'])).

thf('110',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['107','109'])).

thf('111',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['105','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L9E1HMwXM3
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 459 iterations in 0.161s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.60  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.60  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.60  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.60  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(t86_tops_1, conjecture,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.60             ( ![C:$i]:
% 0.21/0.60               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.60                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i]:
% 0.21/0.60        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.60          ( ![B:$i]:
% 0.21/0.60            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60              ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.60                ( ![C:$i]:
% 0.21/0.60                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.21/0.60                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.21/0.60  thf('0', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('split', [status(esa)], ['1'])).
% 0.21/0.60  thf(t3_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i]:
% 0.21/0.60         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('split', [status(esa)], ['1'])).
% 0.21/0.60  thf(t44_tops_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( l1_pre_topc @ A ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      (![X16 : $i, X17 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.60          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.60          | ~ (l1_pre_topc @ X17))),
% 0.21/0.60      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      (((~ (l1_pre_topc @ sk_A)
% 0.21/0.60         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.60  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.60  thf(t1_xboole_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.21/0.60       ( r1_tarski @ A @ C ) ))).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.60          | (r1_tarski @ X0 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      ((![X0 : $i]:
% 0.21/0.60          ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.21/0.60           | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.60  thf('13', plain,
% 0.21/0.60      (![X4 : $i, X6 : $i]:
% 0.21/0.60         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('14', plain,
% 0.21/0.60      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.21/0.60         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.60  thf(t48_tops_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( l1_pre_topc @ A ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60               ( ( r1_tarski @ B @ C ) =>
% 0.21/0.60                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('15', plain,
% 0.21/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.60          | ~ (r1_tarski @ X18 @ X20)
% 0.21/0.60          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ (k1_tops_1 @ X19 @ X20))
% 0.21/0.60          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.21/0.60          | ~ (l1_pre_topc @ X19))),
% 0.21/0.60      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      ((![X0 : $i]:
% 0.21/0.60          (~ (l1_pre_topc @ sk_A)
% 0.21/0.60           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60           | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.21/0.60              (k1_tops_1 @ sk_A @ X0))
% 0.21/0.60           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.60  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      ((![X0 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60           | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_C)) @ 
% 0.21/0.60              (k1_tops_1 @ sk_A @ X0))
% 0.21/0.60           | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('20', plain,
% 0.21/0.60      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.21/0.60      inference('split', [status(esa)], ['19'])).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('split', [status(esa)], ['1'])).
% 0.21/0.60  thf(t55_tops_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( l1_pre_topc @ B ) =>
% 0.21/0.60           ( ![C:$i]:
% 0.21/0.60             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60               ( ![D:$i]:
% 0.21/0.60                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.21/0.60                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.21/0.60                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.21/0.60                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.21/0.60                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X21)
% 0.21/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60          | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.21/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60          | ~ (l1_pre_topc @ X24)
% 0.21/0.60          | ~ (v2_pre_topc @ X24))),
% 0.21/0.60      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      ((![X21 : $i, X22 : $i]:
% 0.21/0.60          (~ (l1_pre_topc @ X21)
% 0.21/0.60           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60           | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60           | ((k1_tops_1 @ X21 @ X22) = (X22))))
% 0.21/0.60         <= ((![X21 : $i, X22 : $i]:
% 0.21/0.60                (~ (l1_pre_topc @ X21)
% 0.21/0.60                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60                 | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60                 | ((k1_tops_1 @ X21 @ X22) = (X22)))))),
% 0.21/0.60      inference('split', [status(esa)], ['22'])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X21)
% 0.21/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60          | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.21/0.60          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60          | ~ (l1_pre_topc @ X24)
% 0.21/0.60          | ~ (v2_pre_topc @ X24))),
% 0.21/0.60      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.21/0.60  thf('26', plain,
% 0.21/0.60      ((![X23 : $i, X24 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60           | ~ (l1_pre_topc @ X24)
% 0.21/0.60           | ~ (v2_pre_topc @ X24)))
% 0.21/0.60         <= ((![X23 : $i, X24 : $i]:
% 0.21/0.60                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60                 | ~ (l1_pre_topc @ X24)
% 0.21/0.60                 | ~ (v2_pre_topc @ X24))))),
% 0.21/0.60      inference('split', [status(esa)], ['25'])).
% 0.21/0.60  thf('27', plain,
% 0.21/0.60      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.60         <= ((![X23 : $i, X24 : $i]:
% 0.21/0.60                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60                 | ~ (l1_pre_topc @ X24)
% 0.21/0.60                 | ~ (v2_pre_topc @ X24))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['24', '26'])).
% 0.21/0.60  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      (~
% 0.21/0.60       (![X23 : $i, X24 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60           | ~ (l1_pre_topc @ X24)
% 0.21/0.60           | ~ (v2_pre_topc @ X24)))),
% 0.21/0.60      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((![X21 : $i, X22 : $i]:
% 0.21/0.60          (~ (l1_pre_topc @ X21)
% 0.21/0.60           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60           | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60           | ((k1_tops_1 @ X21 @ X22) = (X22)))) | 
% 0.21/0.60       (![X23 : $i, X24 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.21/0.60           | ~ (l1_pre_topc @ X24)
% 0.21/0.60           | ~ (v2_pre_topc @ X24)))),
% 0.21/0.60      inference('split', [status(esa)], ['25'])).
% 0.21/0.60  thf('32', plain,
% 0.21/0.60      ((![X21 : $i, X22 : $i]:
% 0.21/0.60          (~ (l1_pre_topc @ X21)
% 0.21/0.60           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60           | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60           | ((k1_tops_1 @ X21 @ X22) = (X22))))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.21/0.60  thf('33', plain,
% 0.21/0.60      (![X21 : $i, X22 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X21)
% 0.21/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.21/0.60          | ~ (v3_pre_topc @ X22 @ X21)
% 0.21/0.60          | ((k1_tops_1 @ X21 @ X22) = (X22)))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['23', '32'])).
% 0.21/0.60  thf('34', plain,
% 0.21/0.60      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.21/0.60         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.21/0.60         | ~ (l1_pre_topc @ sk_A)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['21', '33'])).
% 0.21/0.60  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('36', plain,
% 0.21/0.60      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.21/0.60         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.21/0.60             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['20', '36'])).
% 0.21/0.60  thf('38', plain,
% 0.21/0.60      (![X27 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60          | ((X27) = (k1_xboole_0))
% 0.21/0.60          | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60          | ~ (r1_tarski @ X27 @ sk_B_1)
% 0.21/0.60          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.21/0.60       (![X27 : $i]:
% 0.21/0.60          (((X27) = (k1_xboole_0))
% 0.21/0.60           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60           | ~ (r1_tarski @ X27 @ sk_B_1)))),
% 0.21/0.60      inference('split', [status(esa)], ['38'])).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('41', plain,
% 0.21/0.60      (![X4 : $i, X5 : $i]:
% 0.21/0.60         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('42', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (![X16 : $i, X17 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.21/0.60          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.21/0.60          | ~ (l1_pre_topc @ X17))),
% 0.21/0.60      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.60        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.21/0.60      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.60  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.21/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.60          | (r1_tarski @ X0 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.60  thf('49', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 0.21/0.60          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.60  thf('50', plain,
% 0.21/0.60      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['42', '49'])).
% 0.21/0.60  thf('51', plain,
% 0.21/0.60      (![X4 : $i, X6 : $i]:
% 0.21/0.60         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('52', plain,
% 0.21/0.60      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.21/0.60        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.60  thf('53', plain,
% 0.21/0.60      ((![X27 : $i]:
% 0.21/0.60          (((X27) = (k1_xboole_0))
% 0.21/0.60           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60           | ~ (r1_tarski @ X27 @ sk_B_1)))
% 0.21/0.60         <= ((![X27 : $i]:
% 0.21/0.60                (((X27) = (k1_xboole_0))
% 0.21/0.60                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.21/0.60      inference('split', [status(esa)], ['38'])).
% 0.21/0.60  thf('54', plain,
% 0.21/0.60      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.21/0.60         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.60         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.21/0.60         <= ((![X27 : $i]:
% 0.21/0.60                (((X27) = (k1_xboole_0))
% 0.21/0.60                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.60  thf('55', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.21/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.21/0.60  thf('56', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(fc9_tops_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.21/0.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.60       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.21/0.60  thf('57', plain,
% 0.21/0.60      (![X14 : $i, X15 : $i]:
% 0.21/0.60         (~ (l1_pre_topc @ X14)
% 0.21/0.60          | ~ (v2_pre_topc @ X14)
% 0.21/0.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.21/0.60          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.21/0.60      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.21/0.60  thf('58', plain,
% 0.21/0.60      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.21/0.60        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.60        | ~ (l1_pre_topc @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.21/0.60  thf('59', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('61', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.21/0.60      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.21/0.60  thf('62', plain,
% 0.21/0.60      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.60         <= ((![X27 : $i]:
% 0.21/0.60                (((X27) = (k1_xboole_0))
% 0.21/0.60                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.21/0.60      inference('demod', [status(thm)], ['54', '55', '61'])).
% 0.21/0.60  thf('63', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(t84_tops_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( l1_pre_topc @ A ) =>
% 0.21/0.60       ( ![B:$i]:
% 0.21/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.60           ( ( v2_tops_1 @ B @ A ) <=>
% 0.21/0.60             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.21/0.60  thf('64', plain,
% 0.21/0.60      (![X25 : $i, X26 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.60          | ((k1_tops_1 @ X26 @ X25) != (k1_xboole_0))
% 0.21/0.60          | (v2_tops_1 @ X25 @ X26)
% 0.21/0.60          | ~ (l1_pre_topc @ X26))),
% 0.21/0.60      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.60  thf('65', plain,
% 0.21/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.60        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.60        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.60  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('67', plain,
% 0.21/0.60      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.21/0.60        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.60  thf('68', plain,
% 0.21/0.60      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.21/0.60         <= ((![X27 : $i]:
% 0.21/0.60                (((X27) = (k1_xboole_0))
% 0.21/0.60                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['62', '67'])).
% 0.21/0.60  thf('69', plain,
% 0.21/0.60      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.21/0.60         <= ((![X27 : $i]:
% 0.21/0.60                (((X27) = (k1_xboole_0))
% 0.21/0.60                 | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60                 | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60                 | ~ (r1_tarski @ X27 @ sk_B_1))))),
% 0.21/0.60      inference('simplify', [status(thm)], ['68'])).
% 0.21/0.60  thf('70', plain,
% 0.21/0.60      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('71', plain,
% 0.21/0.60      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.21/0.60      inference('split', [status(esa)], ['70'])).
% 0.21/0.60  thf('72', plain,
% 0.21/0.60      (~
% 0.21/0.60       (![X27 : $i]:
% 0.21/0.60          (((X27) = (k1_xboole_0))
% 0.21/0.60           | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60           | ~ (v3_pre_topc @ X27 @ sk_A)
% 0.21/0.60           | ~ (r1_tarski @ X27 @ sk_B_1))) | 
% 0.21/0.60       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['69', '71'])).
% 0.21/0.60  thf('73', plain,
% 0.21/0.60      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('split', [status(esa)], ['19'])).
% 0.21/0.60  thf('74', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['39', '72', '73'])).
% 0.21/0.60  thf('75', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.21/0.60       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('split', [status(esa)], ['1'])).
% 0.21/0.60  thf('76', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['39', '72', '75'])).
% 0.21/0.60  thf('77', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['37', '74', '76'])).
% 0.21/0.60  thf('78', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['37', '74', '76'])).
% 0.21/0.60  thf('79', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['37', '74', '76'])).
% 0.21/0.60  thf('80', plain,
% 0.21/0.60      ((![X0 : $i]:
% 0.21/0.60          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.60           | ~ (r1_tarski @ sk_C @ X0)))
% 0.21/0.60         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.21/0.60      inference('demod', [status(thm)], ['18', '77', '78', '79'])).
% 0.21/0.60  thf('81', plain,
% 0.21/0.60      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['39', '72', '75'])).
% 0.21/0.60  thf('82', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.60          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.21/0.60          | ~ (r1_tarski @ sk_C @ X0))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.21/0.60  thf('83', plain,
% 0.21/0.60      ((~ (r1_tarski @ sk_C @ sk_B_1)
% 0.21/0.60        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['0', '82'])).
% 0.21/0.60  thf('84', plain,
% 0.21/0.60      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.21/0.60      inference('split', [status(esa)], ['70'])).
% 0.21/0.60  thf('85', plain,
% 0.21/0.60      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('split', [status(esa)], ['70'])).
% 0.21/0.60  thf('86', plain, (((r1_tarski @ sk_C @ sk_B_1))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['39', '72', '85'])).
% 0.21/0.60  thf('87', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['84', '86'])).
% 0.21/0.60  thf('88', plain,
% 0.21/0.60      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.21/0.60      inference('split', [status(esa)], ['38'])).
% 0.21/0.60  thf('89', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('90', plain,
% 0.21/0.60      (![X25 : $i, X26 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.21/0.60          | ~ (v2_tops_1 @ X25 @ X26)
% 0.21/0.60          | ((k1_tops_1 @ X26 @ X25) = (k1_xboole_0))
% 0.21/0.60          | ~ (l1_pre_topc @ X26))),
% 0.21/0.60      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.21/0.60  thf('91', plain,
% 0.21/0.60      ((~ (l1_pre_topc @ sk_A)
% 0.21/0.60        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.21/0.60        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.60  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('93', plain,
% 0.21/0.60      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.21/0.60        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('demod', [status(thm)], ['91', '92'])).
% 0.21/0.60  thf('94', plain,
% 0.21/0.60      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.60         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['88', '93'])).
% 0.21/0.60  thf('95', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['39', '72'])).
% 0.21/0.60  thf('96', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.21/0.60  thf('97', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.21/0.60      inference('demod', [status(thm)], ['83', '87', '96'])).
% 0.21/0.60  thf('98', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.60         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.60          | ~ (r1_tarski @ X1 @ X2)
% 0.21/0.60          | (r1_tarski @ X0 @ X2))),
% 0.21/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.21/0.60  thf('99', plain,
% 0.21/0.60      (![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.60  thf('100', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.60  thf('101', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.21/0.60      inference('demod', [status(thm)], ['99', '100'])).
% 0.21/0.60  thf(t34_mcart_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.60          ( ![B:$i]:
% 0.21/0.60            ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.60                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.21/0.60                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.21/0.60                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.60  thf('102', plain,
% 0.21/0.60      (![X9 : $i]: (((X9) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X9) @ X9))),
% 0.21/0.60      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.21/0.60  thf(t7_ordinal1, axiom,
% 0.21/0.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.60  thf('103', plain,
% 0.21/0.60      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 0.21/0.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.60  thf('104', plain,
% 0.21/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.60  thf('105', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['101', '104'])).
% 0.21/0.60  thf('106', plain,
% 0.21/0.60      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('107', plain,
% 0.21/0.60      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.21/0.60      inference('split', [status(esa)], ['106'])).
% 0.21/0.60  thf('108', plain,
% 0.21/0.60      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.21/0.60      inference('split', [status(esa)], ['106'])).
% 0.21/0.60  thf('109', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.21/0.60      inference('sat_resolution*', [status(thm)], ['39', '72', '108'])).
% 0.21/0.60  thf('110', plain, (((sk_C) != (k1_xboole_0))),
% 0.21/0.60      inference('simpl_trail', [status(thm)], ['107', '109'])).
% 0.21/0.60  thf('111', plain, ($false),
% 0.21/0.60      inference('simplify_reflect-', [status(thm)], ['105', '110'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.21/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
