%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5qZqonErLv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:23 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 690 expanded)
%              Number of leaves         :   24 ( 184 expanded)
%              Depth                    :   20
%              Number of atoms          : 1277 (11043 expanded)
%              Number of equality atoms :   63 ( 466 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_C @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ( r1_tarski @ ( k1_tops_1 @ X15 @ X14 ) @ ( k1_tops_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['20'])).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('23',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) )
   <= ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t55_tops_1])).

thf('26',plain,
    ( ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ~ ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ! [X17: $i,X18: $i] :
        ( ~ ( l1_pre_topc @ X17 )
        | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
        | ~ ( v3_pre_topc @ X18 @ X17 )
        | ( ( k1_tops_1 @ X17 @ X18 )
          = X18 ) )
    | ! [X19: $i,X20: $i] :
        ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
        | ~ ( l1_pre_topc @ X20 )
        | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 ) ) ),
    inference('sat_resolution*',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( ( k1_tops_1 @ X17 @ X18 )
        = X18 ) ) ),
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
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('39',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_C != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('42',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('44',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X13 @ X12 ) @ X12 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('45',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('52',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( v3_pre_topc @ X23 @ sk_A )
      | ~ ( r1_tarski @ X23 @ sk_B )
      | ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['45','46'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_pre_topc @ X10 )
      | ~ ( v2_pre_topc @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X10 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('59',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('65',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k1_tops_1 @ X22 @ X21 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('66',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tops_1 @ sk_B @ sk_A ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('72',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('74',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('75',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['20'])).

thf('76',plain,
    ( ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) )
   <= ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('77',plain,
    ( ( ~ ( r1_tarski @ sk_C @ sk_B )
      | ~ ( v3_pre_topc @ sk_C @ sk_A )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( sk_C = k1_xboole_0 )
      | ~ ( v3_pre_topc @ sk_C @ sk_A ) )
   <= ( ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['74','77'])).

thf('79',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('81',plain,
    ( ( sk_C != sk_C )
   <= ( ( sk_C != k1_xboole_0 )
      & ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
      & ( r1_tarski @ sk_C @ sk_B )
      & ( v3_pre_topc @ sk_C @ sk_A )
      & ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ! [X23: $i] :
          ( ( X23 = k1_xboole_0 )
          | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X23 @ sk_A )
          | ~ ( r1_tarski @ X23 @ sk_B ) )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ! [X23: $i] :
        ( ( X23 = k1_xboole_0 )
        | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X23 @ sk_A )
        | ~ ( r1_tarski @ X23 @ sk_B ) ) ),
    inference(split,[status(esa)],['53'])).

thf('84',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['18'])).

thf('85',plain,(
    v3_pre_topc @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['38','40','41','72','82','83','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['38','84','40','72','82','83','41'])).

thf('87',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = sk_C ),
    inference(simpl_trail,[status(thm)],['37','85','86'])).

thf('88',plain,
    ( ( r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['17','87'])).

thf('89',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference('sat_resolution*',[status(thm)],['84','40','41','72','82','83','38'])).

thf('90',plain,(
    r1_tarski @ sk_C @ ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['53'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( ( k1_tops_1 @ X22 @ X21 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('94',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,(
    v2_tops_1 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['38','84','40','41','72','82','83'])).

thf('99',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,(
    r1_tarski @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['90','99'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('101',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('102',plain,
    ( ( k4_xboole_0 @ sk_C @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['100','101'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('103',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('104',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( sk_C != k1_xboole_0 )
   <= ( sk_C != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('106',plain,(
    sk_C != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','84','41','72','82','83','40'])).

thf('107',plain,(
    sk_C != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['104','107'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5qZqonErLv
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:41:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.44/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.67  % Solved by: fo/fo7.sh
% 0.44/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.67  % done 454 iterations in 0.143s
% 0.44/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.67  % SZS output start Refutation
% 0.44/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.67  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.67  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.44/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.67  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.44/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.44/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.67  thf(t86_tops_1, conjecture,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67           ( ( v2_tops_1 @ B @ A ) <=>
% 0.44/0.67             ( ![C:$i]:
% 0.44/0.67               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67                 ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.44/0.67                   ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.67    (~( ![A:$i]:
% 0.44/0.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.67          ( ![B:$i]:
% 0.44/0.67            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67              ( ( v2_tops_1 @ B @ A ) <=>
% 0.44/0.67                ( ![C:$i]:
% 0.44/0.67                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67                    ( ( ( r1_tarski @ C @ B ) & ( v3_pre_topc @ C @ A ) ) =>
% 0.44/0.67                      ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ) ) ) )),
% 0.44/0.67    inference('cnf.neg', [status(esa)], [t86_tops_1])).
% 0.44/0.67  thf('0', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('1', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(t3_subset, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.44/0.67  thf('2', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.67  thf('3', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.67  thf('4', plain, (((r1_tarski @ sk_C @ sk_B) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('5', plain,
% 0.44/0.67      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('split', [status(esa)], ['4'])).
% 0.44/0.67  thf(t1_xboole_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.67       ( r1_tarski @ A @ C ) ))).
% 0.44/0.67  thf('6', plain,
% 0.44/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.44/0.67         (~ (r1_tarski @ X3 @ X4)
% 0.44/0.67          | ~ (r1_tarski @ X4 @ X5)
% 0.44/0.67          | (r1_tarski @ X3 @ X5))),
% 0.44/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.44/0.67  thf('7', plain,
% 0.44/0.67      ((![X0 : $i]: ((r1_tarski @ sk_C @ X0) | ~ (r1_tarski @ sk_B @ X0)))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.67  thf('8', plain,
% 0.44/0.67      (((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A)))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['3', '7'])).
% 0.44/0.67  thf('9', plain,
% 0.44/0.67      (![X7 : $i, X9 : $i]:
% 0.44/0.67         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.44/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.44/0.67  thf('10', plain,
% 0.44/0.67      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.67  thf(t48_tops_1, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( l1_pre_topc @ A ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67               ( ( r1_tarski @ B @ C ) =>
% 0.44/0.67                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf('11', plain,
% 0.44/0.67      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.44/0.67          | ~ (r1_tarski @ X14 @ X16)
% 0.44/0.67          | (r1_tarski @ (k1_tops_1 @ X15 @ X14) @ (k1_tops_1 @ X15 @ X16))
% 0.44/0.67          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.44/0.67          | ~ (l1_pre_topc @ X15))),
% 0.44/0.67      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.44/0.67  thf('12', plain,
% 0.44/0.67      ((![X0 : $i]:
% 0.44/0.67          (~ (l1_pre_topc @ sk_A)
% 0.44/0.67           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.44/0.67           | ~ (r1_tarski @ sk_C @ X0)))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.67  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('14', plain,
% 0.44/0.67      ((![X0 : $i]:
% 0.44/0.67          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.44/0.67           | ~ (r1_tarski @ sk_C @ X0)))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('15', plain,
% 0.44/0.67      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.44/0.67         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B))))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['0', '14'])).
% 0.44/0.67  thf('16', plain,
% 0.44/0.67      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('split', [status(esa)], ['4'])).
% 0.44/0.67  thf('17', plain,
% 0.44/0.67      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.44/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.44/0.67      inference('demod', [status(thm)], ['15', '16'])).
% 0.44/0.67  thf('18', plain,
% 0.44/0.67      (((v3_pre_topc @ sk_C @ sk_A) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('19', plain,
% 0.44/0.67      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.44/0.67      inference('split', [status(esa)], ['18'])).
% 0.44/0.67  thf('20', plain,
% 0.44/0.67      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.44/0.67        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('21', plain,
% 0.44/0.67      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.44/0.67         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.67      inference('split', [status(esa)], ['20'])).
% 0.44/0.67  thf(t55_tops_1, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( l1_pre_topc @ B ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.67               ( ![D:$i]:
% 0.44/0.67                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.44/0.67                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.44/0.67                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.44/0.67                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.44/0.67                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf('22', plain,
% 0.44/0.67      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.67         (~ (l1_pre_topc @ X17)
% 0.44/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67          | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67          | ((k1_tops_1 @ X17 @ X18) = (X18))
% 0.44/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67          | ~ (l1_pre_topc @ X20)
% 0.44/0.67          | ~ (v2_pre_topc @ X20))),
% 0.44/0.67      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      ((![X17 : $i, X18 : $i]:
% 0.44/0.67          (~ (l1_pre_topc @ X17)
% 0.44/0.67           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67           | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67           | ((k1_tops_1 @ X17 @ X18) = (X18))))
% 0.44/0.67         <= ((![X17 : $i, X18 : $i]:
% 0.44/0.67                (~ (l1_pre_topc @ X17)
% 0.44/0.67                 | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67                 | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67                 | ((k1_tops_1 @ X17 @ X18) = (X18)))))),
% 0.44/0.67      inference('split', [status(esa)], ['22'])).
% 0.44/0.67  thf('24', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('25', plain,
% 0.44/0.67      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.67         (~ (l1_pre_topc @ X17)
% 0.44/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67          | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67          | ((k1_tops_1 @ X17 @ X18) = (X18))
% 0.44/0.67          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67          | ~ (l1_pre_topc @ X20)
% 0.44/0.67          | ~ (v2_pre_topc @ X20))),
% 0.44/0.67      inference('cnf', [status(esa)], [t55_tops_1])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      ((![X19 : $i, X20 : $i]:
% 0.44/0.67          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67           | ~ (l1_pre_topc @ X20)
% 0.44/0.67           | ~ (v2_pre_topc @ X20)))
% 0.44/0.67         <= ((![X19 : $i, X20 : $i]:
% 0.44/0.67                (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67                 | ~ (l1_pre_topc @ X20)
% 0.44/0.67                 | ~ (v2_pre_topc @ X20))))),
% 0.44/0.67      inference('split', [status(esa)], ['25'])).
% 0.44/0.67  thf('27', plain,
% 0.44/0.67      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A)))
% 0.44/0.67         <= ((![X19 : $i, X20 : $i]:
% 0.44/0.67                (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67                 | ~ (l1_pre_topc @ X20)
% 0.44/0.67                 | ~ (v2_pre_topc @ X20))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['24', '26'])).
% 0.44/0.67  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('30', plain,
% 0.44/0.67      (~
% 0.44/0.67       (![X19 : $i, X20 : $i]:
% 0.44/0.67          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67           | ~ (l1_pre_topc @ X20)
% 0.44/0.67           | ~ (v2_pre_topc @ X20)))),
% 0.44/0.67      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      ((![X17 : $i, X18 : $i]:
% 0.44/0.67          (~ (l1_pre_topc @ X17)
% 0.44/0.67           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67           | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67           | ((k1_tops_1 @ X17 @ X18) = (X18)))) | 
% 0.44/0.67       (![X19 : $i, X20 : $i]:
% 0.44/0.67          (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.44/0.67           | ~ (l1_pre_topc @ X20)
% 0.44/0.67           | ~ (v2_pre_topc @ X20)))),
% 0.44/0.67      inference('split', [status(esa)], ['25'])).
% 0.44/0.67  thf('32', plain,
% 0.44/0.67      ((![X17 : $i, X18 : $i]:
% 0.44/0.67          (~ (l1_pre_topc @ X17)
% 0.44/0.67           | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67           | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67           | ((k1_tops_1 @ X17 @ X18) = (X18))))),
% 0.44/0.67      inference('sat_resolution*', [status(thm)], ['30', '31'])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      (![X17 : $i, X18 : $i]:
% 0.44/0.67         (~ (l1_pre_topc @ X17)
% 0.44/0.67          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.44/0.67          | ~ (v3_pre_topc @ X18 @ X17)
% 0.44/0.67          | ((k1_tops_1 @ X17 @ X18) = (X18)))),
% 0.44/0.67      inference('simpl_trail', [status(thm)], ['23', '32'])).
% 0.44/0.67  thf('34', plain,
% 0.44/0.67      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))
% 0.44/0.67         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.44/0.67         | ~ (l1_pre_topc @ sk_A)))
% 0.44/0.67         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.44/0.67      inference('sup-', [status(thm)], ['21', '33'])).
% 0.44/0.67  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('36', plain,
% 0.50/0.67      (((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.50/0.67         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('demod', [status(thm)], ['34', '35'])).
% 0.50/0.67  thf('37', plain,
% 0.50/0.67      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.50/0.67         <= (((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.50/0.67             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['19', '36'])).
% 0.50/0.67  thf('38', plain,
% 0.50/0.67      (((r1_tarski @ sk_C @ sk_B)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['4'])).
% 0.50/0.67  thf('39', plain, ((((sk_C) != (k1_xboole_0)) | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('40', plain,
% 0.50/0.67      (~ (((sk_C) = (k1_xboole_0))) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['39'])).
% 0.50/0.67  thf('41', plain,
% 0.50/0.67      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.50/0.67       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['20'])).
% 0.50/0.67  thf('42', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.67  thf('43', plain,
% 0.50/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(t44_tops_1, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( l1_pre_topc @ A ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.67           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.50/0.67  thf('44', plain,
% 0.50/0.67      (![X12 : $i, X13 : $i]:
% 0.50/0.67         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.50/0.67          | (r1_tarski @ (k1_tops_1 @ X13 @ X12) @ X12)
% 0.50/0.67          | ~ (l1_pre_topc @ X13))),
% 0.50/0.67      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.50/0.67  thf('45', plain,
% 0.50/0.67      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 0.50/0.67      inference('sup-', [status(thm)], ['43', '44'])).
% 0.50/0.67  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('47', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.50/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.67  thf('48', plain,
% 0.50/0.67      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.50/0.67         (~ (r1_tarski @ X3 @ X4)
% 0.50/0.67          | ~ (r1_tarski @ X4 @ X5)
% 0.50/0.67          | (r1_tarski @ X3 @ X5))),
% 0.50/0.67      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.50/0.67  thf('49', plain,
% 0.50/0.67      (![X0 : $i]:
% 0.50/0.67         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 0.50/0.67          | ~ (r1_tarski @ sk_B @ X0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['47', '48'])).
% 0.50/0.67  thf('50', plain,
% 0.50/0.67      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['42', '49'])).
% 0.50/0.67  thf('51', plain,
% 0.50/0.67      (![X7 : $i, X9 : $i]:
% 0.50/0.67         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 0.50/0.67      inference('cnf', [status(esa)], [t3_subset])).
% 0.50/0.67  thf('52', plain,
% 0.50/0.67      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.50/0.67        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['50', '51'])).
% 0.50/0.67  thf('53', plain,
% 0.50/0.67      (![X23 : $i]:
% 0.50/0.67         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67          | ((X23) = (k1_xboole_0))
% 0.50/0.67          | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67          | ~ (r1_tarski @ X23 @ sk_B)
% 0.50/0.67          | (v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('54', plain,
% 0.50/0.67      ((![X23 : $i]:
% 0.50/0.67          (((X23) = (k1_xboole_0))
% 0.50/0.67           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.50/0.67      inference('split', [status(esa)], ['53'])).
% 0.50/0.67  thf('55', plain,
% 0.50/0.67      (((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)
% 0.50/0.67         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.50/0.67         | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['52', '54'])).
% 0.50/0.67  thf('56', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 0.50/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.50/0.67  thf('57', plain,
% 0.50/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(fc9_tops_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.50/0.67         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.50/0.67       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.50/0.67  thf('58', plain,
% 0.50/0.67      (![X10 : $i, X11 : $i]:
% 0.50/0.67         (~ (l1_pre_topc @ X10)
% 0.50/0.67          | ~ (v2_pre_topc @ X10)
% 0.50/0.67          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.50/0.67          | (v3_pre_topc @ (k1_tops_1 @ X10 @ X11) @ X10))),
% 0.50/0.67      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.50/0.67  thf('59', plain,
% 0.50/0.67      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)
% 0.50/0.67        | ~ (v2_pre_topc @ sk_A)
% 0.50/0.67        | ~ (l1_pre_topc @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['57', '58'])).
% 0.50/0.67  thf('60', plain, ((v2_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('62', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_B) @ sk_A)),
% 0.50/0.67      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.50/0.67  thf('63', plain,
% 0.50/0.67      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.50/0.67      inference('demod', [status(thm)], ['55', '56', '62'])).
% 0.50/0.67  thf('64', plain,
% 0.50/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf(t84_tops_1, axiom,
% 0.50/0.67    (![A:$i]:
% 0.50/0.67     ( ( l1_pre_topc @ A ) =>
% 0.50/0.67       ( ![B:$i]:
% 0.50/0.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.50/0.67           ( ( v2_tops_1 @ B @ A ) <=>
% 0.50/0.67             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.50/0.67  thf('65', plain,
% 0.50/0.67      (![X21 : $i, X22 : $i]:
% 0.50/0.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.50/0.67          | ((k1_tops_1 @ X22 @ X21) != (k1_xboole_0))
% 0.50/0.67          | (v2_tops_1 @ X21 @ X22)
% 0.50/0.67          | ~ (l1_pre_topc @ X22))),
% 0.50/0.67      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.50/0.67  thf('66', plain,
% 0.50/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.67        | (v2_tops_1 @ sk_B @ sk_A)
% 0.50/0.67        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['64', '65'])).
% 0.50/0.67  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('68', plain,
% 0.50/0.67      (((v2_tops_1 @ sk_B @ sk_A)
% 0.50/0.67        | ((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.50/0.67      inference('demod', [status(thm)], ['66', '67'])).
% 0.50/0.67  thf('69', plain,
% 0.50/0.67      (((((k1_xboole_0) != (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A)))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['63', '68'])).
% 0.50/0.67  thf('70', plain,
% 0.50/0.67      (((v2_tops_1 @ sk_B @ sk_A))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.50/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.50/0.67  thf('71', plain,
% 0.50/0.67      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['4'])).
% 0.50/0.67  thf('72', plain,
% 0.50/0.67      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.50/0.67       ~
% 0.50/0.67       (![X23 : $i]:
% 0.50/0.67          (((X23) = (k1_xboole_0))
% 0.50/0.67           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67           | ~ (r1_tarski @ X23 @ sk_B)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['70', '71'])).
% 0.50/0.67  thf('73', plain,
% 0.50/0.67      (((v3_pre_topc @ sk_C @ sk_A)) <= (((v3_pre_topc @ sk_C @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['18'])).
% 0.50/0.67  thf('74', plain,
% 0.50/0.67      (((r1_tarski @ sk_C @ sk_B)) <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.50/0.67      inference('split', [status(esa)], ['4'])).
% 0.50/0.67  thf('75', plain,
% 0.50/0.67      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.50/0.67         <= (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('split', [status(esa)], ['20'])).
% 0.50/0.67  thf('76', plain,
% 0.50/0.67      ((![X23 : $i]:
% 0.50/0.67          (((X23) = (k1_xboole_0))
% 0.50/0.67           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67           | ~ (r1_tarski @ X23 @ sk_B)))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))))),
% 0.50/0.67      inference('split', [status(esa)], ['53'])).
% 0.50/0.67  thf('77', plain,
% 0.50/0.67      (((~ (r1_tarski @ sk_C @ sk_B)
% 0.50/0.67         | ~ (v3_pre_topc @ sk_C @ sk_A)
% 0.50/0.67         | ((sk_C) = (k1_xboole_0))))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.50/0.67             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['75', '76'])).
% 0.50/0.67  thf('78', plain,
% 0.50/0.67      (((((sk_C) = (k1_xboole_0)) | ~ (v3_pre_topc @ sk_C @ sk_A)))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.50/0.67             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.50/0.67             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['74', '77'])).
% 0.50/0.67  thf('79', plain,
% 0.50/0.67      ((((sk_C) = (k1_xboole_0)))
% 0.50/0.67         <= ((![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.50/0.67             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.50/0.67             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.50/0.67             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['73', '78'])).
% 0.50/0.67  thf('80', plain,
% 0.50/0.67      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.50/0.67      inference('split', [status(esa)], ['39'])).
% 0.50/0.67  thf('81', plain,
% 0.50/0.67      ((((sk_C) != (sk_C)))
% 0.50/0.67         <= (~ (((sk_C) = (k1_xboole_0))) & 
% 0.50/0.67             (![X23 : $i]:
% 0.50/0.67                (((X23) = (k1_xboole_0))
% 0.50/0.67                 | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67                 | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67                 | ~ (r1_tarski @ X23 @ sk_B))) & 
% 0.50/0.67             ((r1_tarski @ sk_C @ sk_B)) & 
% 0.50/0.67             ((v3_pre_topc @ sk_C @ sk_A)) & 
% 0.50/0.67             ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.50/0.67      inference('sup-', [status(thm)], ['79', '80'])).
% 0.50/0.67  thf('82', plain,
% 0.50/0.67      (~
% 0.50/0.67       (![X23 : $i]:
% 0.50/0.67          (((X23) = (k1_xboole_0))
% 0.50/0.67           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67           | ~ (r1_tarski @ X23 @ sk_B))) | 
% 0.50/0.67       (((sk_C) = (k1_xboole_0))) | ~ ((v3_pre_topc @ sk_C @ sk_A)) | 
% 0.50/0.67       ~ ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.50/0.67       ~ ((r1_tarski @ sk_C @ sk_B))),
% 0.50/0.67      inference('simplify', [status(thm)], ['81'])).
% 0.50/0.67  thf('83', plain,
% 0.50/0.67      (((v2_tops_1 @ sk_B @ sk_A)) | 
% 0.50/0.67       (![X23 : $i]:
% 0.50/0.67          (((X23) = (k1_xboole_0))
% 0.50/0.67           | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.50/0.67           | ~ (v3_pre_topc @ X23 @ sk_A)
% 0.50/0.67           | ~ (r1_tarski @ X23 @ sk_B)))),
% 0.50/0.67      inference('split', [status(esa)], ['53'])).
% 0.50/0.67  thf('84', plain,
% 0.50/0.67      (((v3_pre_topc @ sk_C @ sk_A)) | ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('split', [status(esa)], ['18'])).
% 0.50/0.67  thf('85', plain, (((v3_pre_topc @ sk_C @ sk_A))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)],
% 0.50/0.67                ['38', '40', '41', '72', '82', '83', '84'])).
% 0.50/0.67  thf('86', plain,
% 0.50/0.67      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)],
% 0.50/0.67                ['38', '84', '40', '72', '82', '83', '41'])).
% 0.50/0.67  thf('87', plain, (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['37', '85', '86'])).
% 0.50/0.67  thf('88', plain,
% 0.50/0.67      (((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B)))
% 0.50/0.67         <= (((r1_tarski @ sk_C @ sk_B)))),
% 0.50/0.67      inference('demod', [status(thm)], ['17', '87'])).
% 0.50/0.67  thf('89', plain, (((r1_tarski @ sk_C @ sk_B))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)],
% 0.50/0.67                ['84', '40', '41', '72', '82', '83', '38'])).
% 0.50/0.67  thf('90', plain, ((r1_tarski @ sk_C @ (k1_tops_1 @ sk_A @ sk_B))),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 0.50/0.67  thf('91', plain,
% 0.50/0.67      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.50/0.67      inference('split', [status(esa)], ['53'])).
% 0.50/0.67  thf('92', plain,
% 0.50/0.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('93', plain,
% 0.50/0.67      (![X21 : $i, X22 : $i]:
% 0.50/0.67         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.50/0.67          | ~ (v2_tops_1 @ X21 @ X22)
% 0.50/0.67          | ((k1_tops_1 @ X22 @ X21) = (k1_xboole_0))
% 0.50/0.67          | ~ (l1_pre_topc @ X22))),
% 0.50/0.67      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.50/0.67  thf('94', plain,
% 0.50/0.67      ((~ (l1_pre_topc @ sk_A)
% 0.50/0.67        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.50/0.67        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('sup-', [status(thm)], ['92', '93'])).
% 0.50/0.67  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.50/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.67  thf('96', plain,
% 0.50/0.67      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.50/0.67        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('demod', [status(thm)], ['94', '95'])).
% 0.50/0.67  thf('97', plain,
% 0.50/0.67      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.50/0.67         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.50/0.67      inference('sup-', [status(thm)], ['91', '96'])).
% 0.50/0.67  thf('98', plain, (((v2_tops_1 @ sk_B @ sk_A))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)],
% 0.50/0.67                ['38', '84', '40', '41', '72', '82', '83'])).
% 0.50/0.67  thf('99', plain, (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 0.50/0.67  thf('100', plain, ((r1_tarski @ sk_C @ k1_xboole_0)),
% 0.50/0.67      inference('demod', [status(thm)], ['90', '99'])).
% 0.50/0.67  thf(l32_xboole_1, axiom,
% 0.50/0.67    (![A:$i,B:$i]:
% 0.50/0.67     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.50/0.67  thf('101', plain,
% 0.50/0.67      (![X0 : $i, X2 : $i]:
% 0.50/0.67         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.50/0.67      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.50/0.67  thf('102', plain, (((k4_xboole_0 @ sk_C @ k1_xboole_0) = (k1_xboole_0))),
% 0.50/0.67      inference('sup-', [status(thm)], ['100', '101'])).
% 0.50/0.67  thf(t3_boole, axiom,
% 0.50/0.67    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.50/0.67  thf('103', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.50/0.67      inference('cnf', [status(esa)], [t3_boole])).
% 0.50/0.67  thf('104', plain, (((sk_C) = (k1_xboole_0))),
% 0.50/0.67      inference('demod', [status(thm)], ['102', '103'])).
% 0.50/0.67  thf('105', plain,
% 0.50/0.67      ((((sk_C) != (k1_xboole_0))) <= (~ (((sk_C) = (k1_xboole_0))))),
% 0.50/0.67      inference('split', [status(esa)], ['39'])).
% 0.50/0.67  thf('106', plain, (~ (((sk_C) = (k1_xboole_0)))),
% 0.50/0.67      inference('sat_resolution*', [status(thm)],
% 0.50/0.67                ['38', '84', '41', '72', '82', '83', '40'])).
% 0.50/0.67  thf('107', plain, (((sk_C) != (k1_xboole_0))),
% 0.50/0.67      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 0.50/0.67  thf('108', plain, ($false),
% 0.50/0.67      inference('simplify_reflect-', [status(thm)], ['104', '107'])).
% 0.50/0.67  
% 0.50/0.67  % SZS output end Refutation
% 0.50/0.67  
% 0.50/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
