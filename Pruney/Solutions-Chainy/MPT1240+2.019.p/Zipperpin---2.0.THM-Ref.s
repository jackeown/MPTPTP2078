%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CEQAW2F0NR

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  137 (1139 expanded)
%              Number of leaves         :   28 ( 304 expanded)
%              Depth                    :   26
%              Number of atoms          : 1258 (18595 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t54_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i,C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
          <=> ? [D: $i] :
                ( ( r2_hidden @ B @ D )
                & ( r1_tarski @ D @ C )
                & ( v3_pre_topc @ D @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) )
            <=> ? [D: $i] :
                  ( ( r2_hidden @ B @ D )
                  & ( r1_tarski @ D @ C )
                  & ( v3_pre_topc @ D @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_tops_1])).

thf('0',plain,(
    ! [X26: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X26 @ sk_A )
      | ~ ( r1_tarski @ X26 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X26 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X17 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('10',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X22 @ X21 ) @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('20',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('29',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['20','21'])).

thf('31',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference('sup-',[status(thm)],['13','32'])).

thf('34',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('35',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('37',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ~ ( r1_tarski @ sk_C @ X0 ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) )
   <= ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D )
      | ~ ( r1_tarski @ sk_D @ sk_C )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('46',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_D )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( ( r1_tarski @ sk_D @ sk_C )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C )
      & ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) ) ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,
    ( ~ ! [X26: $i] :
          ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X26 @ sk_A )
          | ~ ( r1_tarski @ X26 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X26 ) )
    | ~ ( r1_tarski @ sk_D @ sk_C )
    | ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['34','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ! [X26: $i] :
        ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X26 @ sk_A )
        | ~ ( r1_tarski @ X26 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X26 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','33','48','49'])).

thf('51',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('53',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['5','7','33','48','49','3'])).

thf('54',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['52','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['56'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','33','48','49','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( r1_tarski @ X23 @ X25 )
      | ( r1_tarski @ ( k1_tops_1 @ X24 @ X23 ) @ ( k1_tops_1 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k1_tops_1 @ X16 @ X15 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k2_pre_topc @ X16 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) ) ) )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('67',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('71',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('72',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','33','48','49','58'])).

thf('74',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['72','73'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['57','59'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('79',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('80',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('83',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['3','5','33','48','49','7'])).

thf('84',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['82','83'])).

thf('85',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['80','81','84'])).

thf('86',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['76','77','85'])).

thf('87',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['69','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','33','48','49','58'])).

thf('89',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('91',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('92',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['3','5','7','33','48','49','58'])).

thf('94',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = sk_D ),
    inference(simpl_trail,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = sk_D ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['64','95'])).

thf('97',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C )
    | ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','96'])).

thf('98',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('99',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['3','7','33','48','49','5'])).

thf('100',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference(simpl_trail,[status(thm)],['98','99'])).

thf('101',plain,(
    r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('104',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['54','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['51','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CEQAW2F0NR
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:23:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 463 iterations in 0.142s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.39/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.39/0.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(t54_tops_1, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59       ( ![B:$i,C:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.39/0.59             ( ?[D:$i]:
% 0.39/0.59               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.39/0.59                 ( v3_pre_topc @ D @ A ) & 
% 0.39/0.59                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.39/0.59          ( ![B:$i,C:$i]:
% 0.39/0.59            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.39/0.59                ( ?[D:$i]:
% 0.39/0.59                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.39/0.59                    ( v3_pre_topc @ D @ A ) & 
% 0.39/0.59                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X26 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59          | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59          | ~ (r2_hidden @ sk_B @ X26)
% 0.39/0.59          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.39/0.59         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (((r2_hidden @ sk_B @ sk_D)
% 0.39/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.39/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      (((r1_tarski @ sk_D @ sk_C)
% 0.39/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('5', plain,
% 0.39/0.59      (((r1_tarski @ sk_D @ sk_C)) | 
% 0.39/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['4'])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (((v3_pre_topc @ sk_D @ sk_A)
% 0.39/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.39/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['6'])).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(fc9_tops_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.39/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.39/0.59       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ X17)
% 0.39/0.59          | ~ (v2_pre_topc @ X17)
% 0.39/0.59          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.39/0.59          | (v3_pre_topc @ (k1_tops_1 @ X17 @ X18) @ X17))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.39/0.59        | ~ (v2_pre_topc @ sk_A)
% 0.39/0.59        | ~ (l1_pre_topc @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.59  thf('11', plain, ((v2_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('13', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.39/0.59      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.39/0.59  thf('14', plain,
% 0.39/0.59      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.39/0.59         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t3_subset, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X10 : $i, X11 : $i]:
% 0.39/0.59         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('17', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(t44_tops_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.39/0.59          | (r1_tarski @ (k1_tops_1 @ X22 @ X21) @ X21)
% 0.39/0.59          | ~ (l1_pre_topc @ X22))),
% 0.39/0.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.39/0.59  thf('20', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.59  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('22', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.39/0.59  thf(t1_xboole_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.59       ( r1_tarski @ A @ C ) ))).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.59          | ~ (r1_tarski @ X1 @ X2)
% 0.39/0.59          | (r1_tarski @ X0 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.59  thf('24', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ X0)
% 0.39/0.59          | ~ (r1_tarski @ sk_C @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['17', '24'])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      (![X10 : $i, X12 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.39/0.59  thf('28', plain,
% 0.39/0.59      ((![X26 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59           | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59           | ~ (r2_hidden @ sk_B @ X26)))
% 0.39/0.59         <= ((![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.39/0.59         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.39/0.59         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.39/0.59         <= ((![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf('30', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['20', '21'])).
% 0.39/0.59  thf('31', plain,
% 0.39/0.59      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.39/0.59         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.39/0.59         <= ((![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      ((~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A))
% 0.39/0.59         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) & 
% 0.39/0.59             (![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['14', '31'])).
% 0.39/0.59  thf('33', plain,
% 0.39/0.59      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 0.39/0.59       ~
% 0.39/0.59       (![X26 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59           | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59           | ~ (r2_hidden @ sk_B @ X26)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['13', '32'])).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['6'])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('36', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['4'])).
% 0.39/0.59  thf('38', plain,
% 0.39/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.59         (~ (r1_tarski @ X0 @ X1)
% 0.39/0.59          | ~ (r1_tarski @ X1 @ X2)
% 0.39/0.59          | (r1_tarski @ X0 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.59  thf('39', plain,
% 0.39/0.59      ((![X0 : $i]: ((r1_tarski @ sk_D @ X0) | ~ (r1_tarski @ sk_C @ X0)))
% 0.39/0.59         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.59  thf('40', plain,
% 0.39/0.59      (((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A)))
% 0.39/0.59         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['36', '39'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (![X10 : $i, X12 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('42', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.59  thf('43', plain,
% 0.39/0.59      ((![X26 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59           | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59           | ~ (r2_hidden @ sk_B @ X26)))
% 0.39/0.59         <= ((![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (((~ (r2_hidden @ sk_B @ sk_D)
% 0.39/0.59         | ~ (r1_tarski @ sk_D @ sk_C)
% 0.39/0.59         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.39/0.59         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.39/0.59             (![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['42', '43'])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['4'])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      (((~ (r2_hidden @ sk_B @ sk_D) | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.39/0.59         <= (((r1_tarski @ sk_D @ sk_C)) & 
% 0.39/0.59             (![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('demod', [status(thm)], ['44', '45'])).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      ((~ (v3_pre_topc @ sk_D @ sk_A))
% 0.39/0.59         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 0.39/0.59             ((r1_tarski @ sk_D @ sk_C)) & 
% 0.39/0.59             (![X26 : $i]:
% 0.39/0.59                (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59                 | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59                 | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59                 | ~ (r2_hidden @ sk_B @ X26))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['35', '46'])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (~
% 0.39/0.59       (![X26 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59           | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59           | ~ (r2_hidden @ sk_B @ X26))) | 
% 0.39/0.59       ~ ((r1_tarski @ sk_D @ sk_C)) | ~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.39/0.59       ~ ((r2_hidden @ sk_B @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['34', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 0.39/0.59       (![X26 : $i]:
% 0.39/0.59          (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59           | ~ (v3_pre_topc @ X26 @ sk_A)
% 0.39/0.59           | ~ (r1_tarski @ X26 @ sk_C)
% 0.39/0.59           | ~ (r2_hidden @ sk_B @ X26)))),
% 0.39/0.59      inference('split', [status(esa)], ['0'])).
% 0.39/0.59  thf('50', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '5', '7', '33', '48', '49'])).
% 0.39/0.59  thf('51', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['1', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.39/0.59      inference('split', [status(esa)], ['2'])).
% 0.39/0.59  thf('53', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['5', '7', '33', '48', '49', '3'])).
% 0.39/0.59  thf('54', plain, ((r2_hidden @ sk_B @ sk_D)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['52', '53'])).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('split', [status(esa)], ['56'])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.39/0.59       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['56'])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '5', '7', '33', '48', '49', '58'])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.39/0.59  thf(t48_tops_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59               ( ( r1_tarski @ B @ C ) =>
% 0.39/0.59                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.39/0.59          | ~ (r1_tarski @ X23 @ X25)
% 0.39/0.59          | (r1_tarski @ (k1_tops_1 @ X24 @ X23) @ (k1_tops_1 @ X24 @ X25))
% 0.39/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.39/0.59          | ~ (l1_pre_topc @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (l1_pre_topc @ sk_A)
% 0.39/0.59          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.39/0.59          | ~ (r1_tarski @ sk_D @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['60', '61'])).
% 0.39/0.59  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('64', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 0.39/0.59          | ~ (r1_tarski @ sk_D @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['62', '63'])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('split', [status(esa)], ['56'])).
% 0.39/0.59  thf(d1_tops_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( k1_tops_1 @ A @ B ) =
% 0.39/0.59             ( k3_subset_1 @
% 0.39/0.59               ( u1_struct_0 @ A ) @ 
% 0.39/0.59               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.39/0.59          | ((k1_tops_1 @ X16 @ X15)
% 0.39/0.59              = (k3_subset_1 @ (u1_struct_0 @ X16) @ 
% 0.39/0.59                 (k2_pre_topc @ X16 @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15))))
% 0.39/0.59          | ~ (l1_pre_topc @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (((~ (l1_pre_topc @ sk_A)
% 0.39/0.59         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.39/0.59             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59                (k2_pre_topc @ sk_A @ 
% 0.39/0.59                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.59  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('69', plain,
% 0.39/0.59      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.39/0.59          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['67', '68'])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('split', [status(esa)], ['56'])).
% 0.39/0.59  thf(dt_k3_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i]:
% 0.39/0.59         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 0.39/0.59          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.39/0.59      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.39/0.59  thf('72', plain,
% 0.39/0.59      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.39/0.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.59  thf('73', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '5', '7', '33', '48', '49', '58'])).
% 0.39/0.59  thf('74', plain,
% 0.39/0.59      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.39/0.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['72', '73'])).
% 0.39/0.59  thf(t52_pre_topc, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.39/0.59             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.39/0.59               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('75', plain,
% 0.39/0.59      (![X13 : $i, X14 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.39/0.59          | ~ (v4_pre_topc @ X13 @ X14)
% 0.39/0.59          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.39/0.59          | ~ (l1_pre_topc @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.39/0.59  thf('76', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.39/0.59            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.39/0.59        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['74', '75'])).
% 0.39/0.59  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('78', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['57', '59'])).
% 0.39/0.59  thf(t30_tops_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_pre_topc @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.59           ( ( v3_pre_topc @ B @ A ) <=>
% 0.39/0.59             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.39/0.59  thf('79', plain,
% 0.39/0.59      (![X19 : $i, X20 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.39/0.59          | ~ (v3_pre_topc @ X19 @ X20)
% 0.39/0.59          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19) @ X20)
% 0.39/0.59          | ~ (l1_pre_topc @ X20))),
% 0.39/0.59      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.39/0.59  thf('80', plain,
% 0.39/0.59      ((~ (l1_pre_topc @ sk_A)
% 0.39/0.59        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.39/0.59        | ~ (v3_pre_topc @ sk_D @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.59  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('82', plain,
% 0.39/0.59      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.39/0.59      inference('split', [status(esa)], ['6'])).
% 0.39/0.59  thf('83', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '5', '33', '48', '49', '7'])).
% 0.39/0.59  thf('84', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['82', '83'])).
% 0.39/0.59  thf('85', plain,
% 0.39/0.59      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 0.39/0.59      inference('demod', [status(thm)], ['80', '81', '84'])).
% 0.39/0.59  thf('86', plain,
% 0.39/0.59      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.39/0.59         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.39/0.59      inference('demod', [status(thm)], ['76', '77', '85'])).
% 0.39/0.59  thf('87', plain,
% 0.39/0.59      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.39/0.59          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['69', '86'])).
% 0.39/0.59  thf('88', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '5', '7', '33', '48', '49', '58'])).
% 0.39/0.59  thf('89', plain,
% 0.39/0.59      (((k1_tops_1 @ sk_A @ sk_D)
% 0.39/0.59         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 0.39/0.59  thf('90', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('split', [status(esa)], ['56'])).
% 0.39/0.59  thf(involutiveness_k3_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.39/0.59  thf('91', plain,
% 0.39/0.59      (![X5 : $i, X6 : $i]:
% 0.39/0.59         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.39/0.59          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.39/0.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.39/0.59  thf('92', plain,
% 0.39/0.59      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 0.39/0.59         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['90', '91'])).
% 0.39/0.59  thf('93', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '5', '7', '33', '48', '49', '58'])).
% 0.39/0.59  thf('94', plain,
% 0.39/0.59      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)) = (sk_D))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['92', '93'])).
% 0.39/0.59  thf('95', plain, (((k1_tops_1 @ sk_A @ sk_D) = (sk_D))),
% 0.39/0.59      inference('sup+', [status(thm)], ['89', '94'])).
% 0.39/0.59  thf('96', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.59          | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ X0))
% 0.39/0.59          | ~ (r1_tarski @ sk_D @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['64', '95'])).
% 0.39/0.59  thf('97', plain,
% 0.39/0.59      ((~ (r1_tarski @ sk_D @ sk_C)
% 0.39/0.59        | (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['55', '96'])).
% 0.39/0.59  thf('98', plain,
% 0.39/0.59      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.39/0.59      inference('split', [status(esa)], ['4'])).
% 0.39/0.59  thf('99', plain, (((r1_tarski @ sk_D @ sk_C))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)],
% 0.39/0.59                ['3', '7', '33', '48', '49', '5'])).
% 0.39/0.59  thf('100', plain, ((r1_tarski @ sk_D @ sk_C)),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['98', '99'])).
% 0.39/0.59  thf('101', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['97', '100'])).
% 0.39/0.59  thf('102', plain,
% 0.39/0.59      (![X10 : $i, X12 : $i]:
% 0.39/0.59         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.39/0.59      inference('cnf', [status(esa)], [t3_subset])).
% 0.39/0.59  thf('103', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['101', '102'])).
% 0.39/0.59  thf(l3_subset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.59       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.39/0.59  thf('104', plain,
% 0.39/0.59      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.59         (~ (r2_hidden @ X7 @ X8)
% 0.39/0.59          | (r2_hidden @ X7 @ X9)
% 0.39/0.59          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.39/0.59      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.39/0.59  thf('105', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.39/0.59          | ~ (r2_hidden @ X0 @ sk_D))),
% 0.39/0.59      inference('sup-', [status(thm)], ['103', '104'])).
% 0.39/0.59  thf('106', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['54', '105'])).
% 0.39/0.59  thf('107', plain, ($false), inference('demod', [status(thm)], ['51', '106'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
