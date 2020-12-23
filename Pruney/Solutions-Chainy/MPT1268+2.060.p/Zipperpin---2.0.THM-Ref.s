%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXfJ4DuOUl

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:24 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 573 expanded)
%              Number of leaves         :   26 ( 163 expanded)
%              Depth                    :   22
%              Number of atoms          : 1078 (8622 expanded)
%              Number of equality atoms :   46 ( 332 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

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

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('4',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
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

thf('10',plain,(
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

thf('11',plain,
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
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
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

thf('14',plain,
    ( ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ! [X23: $i,X24: $i] :
        ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
        | ~ ( l1_pre_topc @ X24 )
        | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
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
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_pre_topc @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X22 @ X21 )
      | ( ( k1_tops_1 @ X21 @ X22 )
        = X22 ) ) ),
    inference(simpl_trail,[status(thm)],['11','20'])).

thf('22',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_C )
        = sk_C )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,(
    ! [X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X30 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X30 @ sk_A )
      | ~ ( r1_tarski @ X30 @ sk_B_1 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    r1_tarski @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X17 @ X16 ) @ X16 )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('33',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['26'])).

thf('42',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X14 @ X15 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('46',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43','49'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( ( k1_tops_1 @ X29 @ X28 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X28 @ X29 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('53',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ! [X30: $i] :
        ( ( X30 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X30 @ sk_A )
        | ~ ( r1_tarski @ X30 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ~ ! [X30: $i] :
          ( ( X30 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X30 @ sk_A )
          | ~ ( r1_tarski @ X30 @ sk_B_1 ) )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('62',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['1'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','60','63'])).

thf('65',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['25','62','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['27','60','63'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['66','67'])).

thf('69',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_B_1 )
    | ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','68'])).

thf('70',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
   <= ( r1_tarski @ sk_C @ sk_B_1 ) ),
    inference(split,[status(esa)],['58'])).

thf('71',plain,
    ( ( r1_tarski @ sk_C @ sk_B_1 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['58'])).

thf('72',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference('sat_resolution*',[status(thm)],['27','60','71'])).

thf('73',plain,(
    r1_tarski @ sk_C @ sk_B_1 ),
    inference(simpl_trail,[status(thm)],['70','72'])).

thf('74',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['26'])).

thf('75',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ~ ( v2_tops_1 @ X28 @ X29 )
      | ( ( k1_tops_1 @ X29 @ X28 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('77',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['27','60'])).

thf('82',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['69','73','82'])).

thf('84',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('86',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_C @ X0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('88',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('89',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('95',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['27','60','94'])).

thf('96',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['93','95'])).

thf('97',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uXfJ4DuOUl
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:48:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.43/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.61  % Solved by: fo/fo7.sh
% 0.43/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.61  % done 403 iterations in 0.142s
% 0.43/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.61  % SZS output start Refutation
% 0.43/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.43/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.43/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.43/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.43/0.61  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.43/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.43/0.61  thf(t86_tops_1, conjecture,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( v2_tops_1 @ B @ A ) <=>
% 0.43/0.61             ( ![C:$i]:
% 0.43/0.61               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.43/0.61                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.61    (~( ![A:$i]:
% 0.43/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61          ( ![B:$i]:
% 0.43/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61              ( ( v2_tops_1 @ B @ A ) <=>
% 0.43/0.61                ( ![C:$i]:
% 0.43/0.61                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.43/0.61                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.43/0.61    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.43/0.61  thf('0', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('1', plain,
% 0.43/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('2', plain,
% 0.43/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('split', [status(esa)], ['1'])).
% 0.43/0.61  thf(t48_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_pre_topc @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61               ( ( r1_tarski @ B @ C ) =>
% 0.43/0.61                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('3', plain,
% 0.43/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.43/0.61          | ~ (r1_tarski @ X18 @ X20)
% 0.43/0.61          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ (k1_tops_1 @ X19 @ X20))
% 0.43/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.43/0.61          | ~ (l1_pre_topc @ X19))),
% 0.43/0.61      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.43/0.61  thf('4', plain,
% 0.43/0.61      ((![X0 : $i]:
% 0.43/0.61          (~ (l1_pre_topc @ sk_A)
% 0.43/0.61           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.43/0.61           | ~ (r1_tarski @ sk_C @ X0)))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.61  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('6', plain,
% 0.43/0.61      ((![X0 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.43/0.61           | ~ (r1_tarski @ sk_C @ X0)))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('demod', [status(thm)], ['4', '5'])).
% 0.43/0.61  thf('7', plain,
% 0.43/0.61      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('8', plain,
% 0.43/0.61      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['7'])).
% 0.43/0.61  thf('9', plain,
% 0.43/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('split', [status(esa)], ['1'])).
% 0.43/0.61  thf(t55_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( l1_pre_topc @ B ) =>
% 0.43/0.61           ( ![C:$i]:
% 0.43/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61               ( ![D:$i]:
% 0.43/0.61                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.43/0.61                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.43/0.61                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.43/0.61                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.43/0.61                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.43/0.61  thf('10', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X21)
% 0.43/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61          | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.43/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61          | ~ (l1_pre_topc @ X24)
% 0.43/0.61          | ~ (v2_pre_topc @ X24))),
% 0.43/0.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.43/0.61  thf('11', plain,
% 0.43/0.61      ((![X21 : $i, X22 : $i]:
% 0.43/0.61          (~ (l1_pre_topc @ X21)
% 0.43/0.61           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61           | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61           | ((k1_tops_1 @ X21 @ X22) = (X22))))
% 0.43/0.61         <= ((![X21 : $i, X22 : $i]:
% 0.43/0.61                (~ (l1_pre_topc @ X21)
% 0.43/0.61                 | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61                 | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61                 | ((k1_tops_1 @ X21 @ X22) = (X22)))))),
% 0.43/0.61      inference('split', [status(esa)], ['10'])).
% 0.43/0.61  thf('12', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('13', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X21)
% 0.43/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61          | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61          | ((k1_tops_1 @ X21 @ X22) = (X22))
% 0.43/0.61          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61          | ~ (l1_pre_topc @ X24)
% 0.43/0.61          | ~ (v2_pre_topc @ X24))),
% 0.43/0.61      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.43/0.61  thf('14', plain,
% 0.43/0.61      ((![X23 : $i, X24 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61           | ~ (l1_pre_topc @ X24)
% 0.43/0.61           | ~ (v2_pre_topc @ X24)))
% 0.43/0.61         <= ((![X23 : $i, X24 : $i]:
% 0.43/0.61                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61                 | ~ (l1_pre_topc @ X24)
% 0.43/0.61                 | ~ (v2_pre_topc @ X24))))),
% 0.43/0.61      inference('split', [status(esa)], ['13'])).
% 0.43/0.61  thf('15', plain,
% 0.43/0.61      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.43/0.61         <= ((![X23 : $i, X24 : $i]:
% 0.43/0.61                (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61                 | ~ (l1_pre_topc @ X24)
% 0.43/0.61                 | ~ (v2_pre_topc @ X24))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['12', '14'])).
% 0.43/0.61  thf('16', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('18', plain,
% 0.43/0.61      (~
% 0.43/0.61       (![X23 : $i, X24 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61           | ~ (l1_pre_topc @ X24)
% 0.43/0.61           | ~ (v2_pre_topc @ X24)))),
% 0.43/0.61      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.43/0.61  thf('19', plain,
% 0.43/0.61      ((![X21 : $i, X22 : $i]:
% 0.43/0.61          (~ (l1_pre_topc @ X21)
% 0.43/0.61           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61           | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61           | ((k1_tops_1 @ X21 @ X22) = (X22)))) | 
% 0.43/0.61       (![X23 : $i, X24 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.43/0.61           | ~ (l1_pre_topc @ X24)
% 0.43/0.61           | ~ (v2_pre_topc @ X24)))),
% 0.43/0.61      inference('split', [status(esa)], ['13'])).
% 0.43/0.61  thf('20', plain,
% 0.43/0.61      ((![X21 : $i, X22 : $i]:
% 0.43/0.61          (~ (l1_pre_topc @ X21)
% 0.43/0.61           | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61           | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61           | ((k1_tops_1 @ X21 @ X22) = (X22))))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.43/0.61  thf('21', plain,
% 0.43/0.61      (![X21 : $i, X22 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X21)
% 0.43/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.43/0.61          | ~ (v3_pre_topc @ X22 @ X21)
% 0.43/0.61          | ((k1_tops_1 @ X21 @ X22) = (X22)))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['11', '20'])).
% 0.43/0.61  thf('22', plain,
% 0.43/0.61      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.43/0.61         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.43/0.61         | ~ (l1_pre_topc @ sk_A)))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['9', '21'])).
% 0.43/0.61  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('24', plain,
% 0.43/0.61      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('demod', [status(thm)], ['22', '23'])).
% 0.43/0.61  thf('25', plain,
% 0.43/0.61      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.43/0.61         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.43/0.61             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['8', '24'])).
% 0.43/0.61  thf('26', plain,
% 0.43/0.61      (![X30 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61          | ((X30) = (k1_xboole_0))
% 0.43/0.61          | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61          | ~ (r1_tarski @ X30 @ sk_B_1)
% 0.43/0.61          | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('27', plain,
% 0.43/0.61      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.43/0.61       (![X30 : $i]:
% 0.43/0.61          (((X30) = (k1_xboole_0))
% 0.43/0.61           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61           | ~ (r1_tarski @ X30 @ sk_B_1)))),
% 0.43/0.61      inference('split', [status(esa)], ['26'])).
% 0.43/0.61  thf('28', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t3_subset, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.43/0.61  thf('29', plain,
% 0.43/0.61      (![X6 : $i, X7 : $i]:
% 0.43/0.61         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.61  thf('30', plain, ((r1_tarski @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.43/0.61  thf('31', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t44_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_pre_topc @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.43/0.61  thf('32', plain,
% 0.43/0.61      (![X16 : $i, X17 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.43/0.61          | (r1_tarski @ (k1_tops_1 @ X17 @ X16) @ X16)
% 0.43/0.61          | ~ (l1_pre_topc @ X17))),
% 0.43/0.61      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.43/0.61  thf('33', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1))),
% 0.43/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.61  thf('34', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('35', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.43/0.61  thf(t1_xboole_1, axiom,
% 0.43/0.61    (![A:$i,B:$i,C:$i]:
% 0.43/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.43/0.61       ( r1_tarski @ A @ C ) ))).
% 0.43/0.61  thf('36', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X1 @ X2)
% 0.43/0.61          | ~ (r1_tarski @ X2 @ X3)
% 0.43/0.61          | (r1_tarski @ X1 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.43/0.61  thf('37', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ X0)
% 0.43/0.61          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['35', '36'])).
% 0.43/0.61  thf('38', plain,
% 0.43/0.61      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['30', '37'])).
% 0.43/0.61  thf('39', plain,
% 0.43/0.61      (![X6 : $i, X8 : $i]:
% 0.43/0.61         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.43/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.43/0.61  thf('40', plain,
% 0.43/0.61      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.43/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.43/0.61  thf('41', plain,
% 0.43/0.61      ((![X30 : $i]:
% 0.43/0.61          (((X30) = (k1_xboole_0))
% 0.43/0.61           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61           | ~ (r1_tarski @ X30 @ sk_B_1)))
% 0.43/0.61         <= ((![X30 : $i]:
% 0.43/0.61                (((X30) = (k1_xboole_0))
% 0.43/0.61                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 0.43/0.61      inference('split', [status(esa)], ['26'])).
% 0.43/0.61  thf('42', plain,
% 0.43/0.61      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)
% 0.43/0.61         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.61         | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))
% 0.43/0.61         <= ((![X30 : $i]:
% 0.43/0.61                (((X30) = (k1_xboole_0))
% 0.43/0.61                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.43/0.61  thf('43', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_B_1)),
% 0.43/0.61      inference('demod', [status(thm)], ['33', '34'])).
% 0.43/0.61  thf('44', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(fc9_tops_1, axiom,
% 0.43/0.61    (![A:$i,B:$i]:
% 0.43/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.43/0.61         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.43/0.61       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.43/0.61  thf('45', plain,
% 0.43/0.61      (![X14 : $i, X15 : $i]:
% 0.43/0.61         (~ (l1_pre_topc @ X14)
% 0.43/0.61          | ~ (v2_pre_topc @ X14)
% 0.43/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.43/0.61          | (v3_pre_topc @ (k1_tops_1 @ X14 @ X15) @ X14))),
% 0.43/0.61      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.43/0.61  thf('46', plain,
% 0.43/0.61      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)
% 0.43/0.61        | ~ (v2_pre_topc @ sk_A)
% 0.43/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.61  thf('47', plain, ((v2_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('49', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.43/0.61      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.43/0.61  thf('50', plain,
% 0.43/0.61      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.43/0.61         <= ((![X30 : $i]:
% 0.43/0.61                (((X30) = (k1_xboole_0))
% 0.43/0.61                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 0.43/0.61      inference('demod', [status(thm)], ['42', '43', '49'])).
% 0.43/0.61  thf('51', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf(t84_tops_1, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ( l1_pre_topc @ A ) =>
% 0.43/0.61       ( ![B:$i]:
% 0.43/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.43/0.61           ( ( v2_tops_1 @ B @ A ) <=>
% 0.43/0.61             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.43/0.61  thf('52', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.43/0.61          | ((k1_tops_1 @ X29 @ X28) != (k1_xboole_0))
% 0.43/0.61          | (v2_tops_1 @ X28 @ X29)
% 0.43/0.61          | ~ (l1_pre_topc @ X29))),
% 0.43/0.61      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.43/0.61  thf('53', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.43/0.61        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.43/0.61  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('55', plain,
% 0.43/0.61      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.43/0.61        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.43/0.61      inference('demod', [status(thm)], ['53', '54'])).
% 0.43/0.61  thf('56', plain,
% 0.43/0.61      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.43/0.61         <= ((![X30 : $i]:
% 0.43/0.61                (((X30) = (k1_xboole_0))
% 0.43/0.61                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 0.43/0.61      inference('sup-', [status(thm)], ['50', '55'])).
% 0.43/0.61  thf('57', plain,
% 0.43/0.61      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.43/0.61         <= ((![X30 : $i]:
% 0.43/0.61                (((X30) = (k1_xboole_0))
% 0.43/0.61                 | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61                 | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61                 | ~ (r1_tarski @ X30 @ sk_B_1))))),
% 0.43/0.61      inference('simplify', [status(thm)], ['56'])).
% 0.43/0.61  thf('58', plain,
% 0.43/0.61      (((r1_tarski @ sk_C @ sk_B_1) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('59', plain,
% 0.43/0.61      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['58'])).
% 0.43/0.61  thf('60', plain,
% 0.43/0.61      (~
% 0.43/0.61       (![X30 : $i]:
% 0.43/0.61          (((X30) = (k1_xboole_0))
% 0.43/0.61           | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61           | ~ (v3_pre_topc @ X30 @ sk_A)
% 0.43/0.61           | ~ (r1_tarski @ X30 @ sk_B_1))) | 
% 0.43/0.61       ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['57', '59'])).
% 0.43/0.61  thf('61', plain,
% 0.43/0.61      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['7'])).
% 0.43/0.61  thf('62', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['27', '60', '61'])).
% 0.43/0.61  thf('63', plain,
% 0.43/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.43/0.61       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['1'])).
% 0.43/0.61  thf('64', plain,
% 0.43/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['27', '60', '63'])).
% 0.43/0.61  thf('65', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['25', '62', '64'])).
% 0.43/0.61  thf('66', plain,
% 0.43/0.61      ((![X0 : $i]:
% 0.43/0.61          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61           | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.43/0.61           | ~ (r1_tarski @ sk_C @ X0)))
% 0.43/0.61         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.43/0.61      inference('demod', [status(thm)], ['6', '65'])).
% 0.43/0.61  thf('67', plain,
% 0.43/0.61      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['27', '60', '63'])).
% 0.43/0.61  thf('68', plain,
% 0.43/0.61      (![X0 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.43/0.61          | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ X0))
% 0.43/0.61          | ~ (r1_tarski @ sk_C @ X0))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['66', '67'])).
% 0.43/0.61  thf('69', plain,
% 0.43/0.61      ((~ (r1_tarski @ sk_C @ sk_B_1)
% 0.43/0.61        | (r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['0', '68'])).
% 0.43/0.61  thf('70', plain,
% 0.43/0.61      (((r1_tarski @ sk_C @ sk_B_1)) <= (((r1_tarski @ sk_C @ sk_B_1)))),
% 0.43/0.61      inference('split', [status(esa)], ['58'])).
% 0.43/0.61  thf('71', plain,
% 0.43/0.61      (((r1_tarski @ sk_C @ sk_B_1)) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['58'])).
% 0.43/0.61  thf('72', plain, (((r1_tarski @ sk_C @ sk_B_1))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['27', '60', '71'])).
% 0.43/0.61  thf('73', plain, ((r1_tarski @ sk_C @ sk_B_1)),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['70', '72'])).
% 0.43/0.61  thf('74', plain,
% 0.43/0.61      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('split', [status(esa)], ['26'])).
% 0.43/0.61  thf('75', plain,
% 0.43/0.61      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('76', plain,
% 0.43/0.61      (![X28 : $i, X29 : $i]:
% 0.43/0.61         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 0.43/0.61          | ~ (v2_tops_1 @ X28 @ X29)
% 0.43/0.61          | ((k1_tops_1 @ X29 @ X28) = (k1_xboole_0))
% 0.43/0.61          | ~ (l1_pre_topc @ X29))),
% 0.43/0.61      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.43/0.61  thf('77', plain,
% 0.43/0.61      ((~ (l1_pre_topc @ sk_A)
% 0.43/0.61        | ((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.43/0.61        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.43/0.61  thf('78', plain, ((l1_pre_topc @ sk_A)),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('79', plain,
% 0.43/0.61      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.43/0.61        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('demod', [status(thm)], ['77', '78'])).
% 0.43/0.61  thf('80', plain,
% 0.43/0.61      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.43/0.61         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['74', '79'])).
% 0.43/0.61  thf('81', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['27', '60'])).
% 0.43/0.61  thf('82', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 0.43/0.61  thf('83', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.43/0.61      inference('demod', [status(thm)], ['69', '73', '82'])).
% 0.43/0.61  thf('84', plain,
% 0.43/0.61      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.43/0.61         (~ (r1_tarski @ X1 @ X2)
% 0.43/0.61          | ~ (r1_tarski @ X2 @ X3)
% 0.43/0.61          | (r1_tarski @ X1 @ X3))),
% 0.43/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.43/0.61  thf('85', plain,
% 0.43/0.61      (![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.43/0.61  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.43/0.61  thf('86', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.43/0.61      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.43/0.61  thf('87', plain, (![X0 : $i]: (r1_tarski @ sk_C @ X0)),
% 0.43/0.61      inference('demod', [status(thm)], ['85', '86'])).
% 0.43/0.61  thf(t7_xboole_0, axiom,
% 0.43/0.61    (![A:$i]:
% 0.43/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.61          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.61  thf('88', plain,
% 0.43/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.61  thf(t7_ordinal1, axiom,
% 0.43/0.61    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.43/0.61  thf('89', plain,
% 0.43/0.61      (![X12 : $i, X13 : $i]:
% 0.43/0.61         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 0.43/0.61      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.43/0.61  thf('90', plain,
% 0.43/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.43/0.61      inference('sup-', [status(thm)], ['88', '89'])).
% 0.43/0.61  thf('91', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.61      inference('sup-', [status(thm)], ['87', '90'])).
% 0.43/0.61  thf('92', plain,
% 0.43/0.61      ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.61  thf('93', plain,
% 0.43/0.61      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.43/0.61      inference('split', [status(esa)], ['92'])).
% 0.43/0.61  thf('94', plain,
% 0.43/0.61      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.43/0.61      inference('split', [status(esa)], ['92'])).
% 0.43/0.61  thf('95', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.43/0.61      inference('sat_resolution*', [status(thm)], ['27', '60', '94'])).
% 0.43/0.61  thf('96', plain, (((sk_C) != (k1_xboole_0))),
% 0.43/0.61      inference('simpl_trail', [status(thm)], ['93', '95'])).
% 0.43/0.61  thf('97', plain, ($false),
% 0.43/0.61      inference('simplify_reflect-', [status(thm)], ['91', '96'])).
% 0.43/0.61  
% 0.43/0.61  % SZS output end Refutation
% 0.43/0.61  
% 0.43/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
