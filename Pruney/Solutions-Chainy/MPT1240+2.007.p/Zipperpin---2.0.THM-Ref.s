%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8becAGZzrr

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:06 EST 2020

% Result     : Theorem 0.97s
% Output     : Refutation 0.97s
% Verified   : 
% Statistics : Number of formulae       :  168 (1302 expanded)
%              Number of leaves         :   34 ( 348 expanded)
%              Depth                    :   20
%              Number of atoms          : 1439 (22231 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

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
    ! [X37: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X37 @ sk_A )
      | ~ ( r1_tarski @ X37 @ sk_C )
      | ~ ( r2_hidden @ sk_B @ X37 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X37 @ sk_A )
        | ~ ( r1_tarski @ X37 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X37 @ sk_A )
        | ~ ( r1_tarski @ X37 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X37 ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X37 @ sk_A )
        | ~ ( r1_tarski @ X37 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X37 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X37 @ sk_A )
        | ~ ( r1_tarski @ X37 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X37 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X28 @ X29 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('14',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X37 @ sk_A )
        | ~ ( r1_tarski @ X37 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X37 ) ) ),
    inference(demod,[status(thm)],['11','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('21',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
   <= ! [X37: $i] :
        ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X37 @ sk_A )
        | ~ ( r1_tarski @ X37 @ sk_C )
        | ~ ( r2_hidden @ sk_B @ X37 ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,
    ( ~ ! [X37: $i] :
          ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X37 @ sk_A )
          | ~ ( r1_tarski @ X37 @ sk_C )
          | ~ ( r2_hidden @ sk_B @ X37 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    r1_tarski @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( ( k2_xboole_0 @ sk_D @ sk_C )
      = sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ sk_C @ X0 )
        | ( r1_tarski @ sk_D @ X0 ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l1_pre_topc @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('42',plain,
    ( ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['32'])).

thf('46',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','25','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('48',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r1_tarski @ X34 @ X36 )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_D ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_D ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_C )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_D ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','51'])).

thf('53',plain,
    ( ( r1_tarski @ sk_D @ sk_C )
   <= ( r1_tarski @ sk_D @ sk_C ) ),
    inference(split,[status(esa)],['32'])).

thf('54',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','25','45'])).

thf('55',plain,(
    r1_tarski @ sk_D @ sk_C ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('59',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['56'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','62'])).

thf('64',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('65',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X10 )
      | ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k1_tops_1 @ sk_A @ sk_D ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['52','67'])).

thf('69',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ),
    inference(simpl_trail,[status(thm)],['61','63'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('70',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('71',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_D ) )
    | ( sk_D
      = ( k1_tops_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','62'])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ X16 @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ( r1_tarski @ sk_D @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( r1_tarski @ sk_D @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,
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

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('82',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','62'])).

thf('86',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ),
    inference(simpl_trail,[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['74','75'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('88',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('89',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

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

thf('90',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('91',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['56'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('94',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( v3_pre_topc @ X30 @ X31 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X31 ) @ X30 ) @ X31 )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('95',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['98'])).

thf('101',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','25','100'])).

thf('102',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['99','101'])).

thf('103',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['97','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','62'])).

thf('105',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['103','104'])).

thf('106',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['91','92','105'])).

thf('107',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['86','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('109',plain,(
    r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['79','107','108'])).

thf('110',plain,
    ( sk_D
    = ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['71','109'])).

thf('111',plain,
    ( sk_D
    = ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['71','109'])).

thf('112',plain,(
    r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['68','110','111'])).

thf('113',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('114',plain,
    ( ( k2_xboole_0 @ sk_D @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('116',plain,(
    ! [X11: $i,X13: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X11 ) @ X13 )
      | ~ ( r2_hidden @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('117',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('119',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_D )
      = sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('121',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k1_tarski @ sk_B ) @ ( k2_xboole_0 @ sk_D @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup+',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k1_tarski @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('127',plain,
    ( ! [X0: $i] :
        ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('129',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','25','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ sk_D @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['127','129'])).

thf('131',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup+',[status(thm)],['114','130'])).

thf('132',plain,(
    $false ),
    inference(demod,[status(thm)],['27','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8becAGZzrr
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:06:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.97/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.97/1.20  % Solved by: fo/fo7.sh
% 0.97/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.97/1.20  % done 1814 iterations in 0.740s
% 0.97/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.97/1.20  % SZS output start Refutation
% 0.97/1.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.97/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.97/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.97/1.20  thf(sk_D_type, type, sk_D: $i).
% 0.97/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.97/1.20  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.97/1.20  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.97/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.97/1.20  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.97/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.97/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.97/1.20  thf(sk_B_type, type, sk_B: $i).
% 0.97/1.20  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.97/1.20  thf(sk_C_type, type, sk_C: $i).
% 0.97/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.97/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.97/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.97/1.20  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.97/1.20  thf(t54_tops_1, conjecture,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.97/1.20       ( ![B:$i,C:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.97/1.20             ( ?[D:$i]:
% 0.97/1.20               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.97/1.20                 ( v3_pre_topc @ D @ A ) & 
% 0.97/1.20                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.97/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.97/1.20    (~( ![A:$i]:
% 0.97/1.20        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.97/1.20          ( ![B:$i,C:$i]:
% 0.97/1.20            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 0.97/1.20                ( ?[D:$i]:
% 0.97/1.20                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 0.97/1.20                    ( v3_pre_topc @ D @ A ) & 
% 0.97/1.20                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.97/1.20    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 0.97/1.20  thf('0', plain,
% 0.97/1.20      (![X37 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20          | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20          | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20          | ~ (r2_hidden @ sk_B @ X37)
% 0.97/1.20          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('1', plain,
% 0.97/1.20      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.97/1.20         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.97/1.20      inference('split', [status(esa)], ['0'])).
% 0.97/1.20  thf('2', plain,
% 0.97/1.20      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))) | 
% 0.97/1.20       (![X37 : $i]:
% 0.97/1.20          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20           | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20           | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20           | ~ (r2_hidden @ sk_B @ X37)))),
% 0.97/1.20      inference('split', [status(esa)], ['0'])).
% 0.97/1.20  thf('3', plain,
% 0.97/1.20      (((r2_hidden @ sk_B @ sk_D)
% 0.97/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('4', plain,
% 0.97/1.20      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.97/1.20         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))))),
% 0.97/1.20      inference('split', [status(esa)], ['3'])).
% 0.97/1.20  thf('5', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(dt_k1_tops_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( ( l1_pre_topc @ A ) & 
% 0.97/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.97/1.20       ( m1_subset_1 @
% 0.97/1.20         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.97/1.20  thf('6', plain,
% 0.97/1.20      (![X26 : $i, X27 : $i]:
% 0.97/1.20         (~ (l1_pre_topc @ X26)
% 0.97/1.20          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.97/1.20          | (m1_subset_1 @ (k1_tops_1 @ X26 @ X27) @ 
% 0.97/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.97/1.20      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.97/1.20  thf('7', plain,
% 0.97/1.20      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.97/1.20         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20        | ~ (l1_pre_topc @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 0.97/1.20  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('9', plain,
% 0.97/1.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.97/1.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('demod', [status(thm)], ['7', '8'])).
% 0.97/1.20  thf('10', plain,
% 0.97/1.20      ((![X37 : $i]:
% 0.97/1.20          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20           | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20           | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20           | ~ (r2_hidden @ sk_B @ X37)))
% 0.97/1.20         <= ((![X37 : $i]:
% 0.97/1.20                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20                 | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20                 | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20                 | ~ (r2_hidden @ sk_B @ X37))))),
% 0.97/1.20      inference('split', [status(esa)], ['0'])).
% 0.97/1.20  thf('11', plain,
% 0.97/1.20      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.97/1.20         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)
% 0.97/1.20         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)))
% 0.97/1.20         <= ((![X37 : $i]:
% 0.97/1.20                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20                 | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20                 | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20                 | ~ (r2_hidden @ sk_B @ X37))))),
% 0.97/1.20      inference('sup-', [status(thm)], ['9', '10'])).
% 0.97/1.20  thf('12', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(fc9_tops_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.97/1.20         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.97/1.20       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.97/1.20  thf('13', plain,
% 0.97/1.20      (![X28 : $i, X29 : $i]:
% 0.97/1.20         (~ (l1_pre_topc @ X28)
% 0.97/1.20          | ~ (v2_pre_topc @ X28)
% 0.97/1.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.97/1.20          | (v3_pre_topc @ (k1_tops_1 @ X28 @ X29) @ X28))),
% 0.97/1.20      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.97/1.20  thf('14', plain,
% 0.97/1.20      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.97/1.20        | ~ (v2_pre_topc @ sk_A)
% 0.97/1.20        | ~ (l1_pre_topc @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['12', '13'])).
% 0.97/1.20  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('17', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.97/1.20      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.97/1.20  thf('18', plain,
% 0.97/1.20      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.97/1.20         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)))
% 0.97/1.20         <= ((![X37 : $i]:
% 0.97/1.20                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20                 | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20                 | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20                 | ~ (r2_hidden @ sk_B @ X37))))),
% 0.97/1.20      inference('demod', [status(thm)], ['11', '17'])).
% 0.97/1.20  thf('19', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(t44_tops_1, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( l1_pre_topc @ A ) =>
% 0.97/1.20       ( ![B:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 0.97/1.20  thf('20', plain,
% 0.97/1.20      (![X32 : $i, X33 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.97/1.20          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.97/1.20          | ~ (l1_pre_topc @ X33))),
% 0.97/1.20      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.97/1.20  thf('21', plain,
% 0.97/1.20      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 0.97/1.20      inference('sup-', [status(thm)], ['19', '20'])).
% 0.97/1.20  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('23', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 0.97/1.20      inference('demod', [status(thm)], ['21', '22'])).
% 0.97/1.20  thf('24', plain,
% 0.97/1.20      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))
% 0.97/1.20         <= ((![X37 : $i]:
% 0.97/1.20                (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20                 | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20                 | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20                 | ~ (r2_hidden @ sk_B @ X37))))),
% 0.97/1.20      inference('demod', [status(thm)], ['18', '23'])).
% 0.97/1.20  thf('25', plain,
% 0.97/1.20      (~
% 0.97/1.20       (![X37 : $i]:
% 0.97/1.20          (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20           | ~ (v3_pre_topc @ X37 @ sk_A)
% 0.97/1.20           | ~ (r1_tarski @ X37 @ sk_C)
% 0.97/1.20           | ~ (r2_hidden @ sk_B @ X37))) | 
% 0.97/1.20       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['4', '24'])).
% 0.97/1.20  thf('26', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.97/1.20  thf('27', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.97/1.20  thf('28', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('29', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf(t3_subset, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.97/1.20  thf('30', plain,
% 0.97/1.20      (![X19 : $i, X20 : $i]:
% 0.97/1.20         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.97/1.20      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.20  thf('31', plain, ((r1_tarski @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['29', '30'])).
% 0.97/1.20  thf('32', plain,
% 0.97/1.20      (((r1_tarski @ sk_D @ sk_C)
% 0.97/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('33', plain,
% 0.97/1.20      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('split', [status(esa)], ['32'])).
% 0.97/1.20  thf(t12_xboole_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.97/1.20  thf('34', plain,
% 0.97/1.20      (![X6 : $i, X7 : $i]:
% 0.97/1.20         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.97/1.20      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.20  thf('35', plain,
% 0.97/1.20      ((((k2_xboole_0 @ sk_D @ sk_C) = (sk_C)))
% 0.97/1.20         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['33', '34'])).
% 0.97/1.20  thf(t11_xboole_1, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i]:
% 0.97/1.20     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.97/1.20  thf('36', plain,
% 0.97/1.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.20         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.97/1.20      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.20  thf('37', plain,
% 0.97/1.20      ((![X0 : $i]: (~ (r1_tarski @ sk_C @ X0) | (r1_tarski @ sk_D @ X0)))
% 0.97/1.20         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 0.97/1.20  thf('38', plain,
% 0.97/1.20      (((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A)))
% 0.97/1.20         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['31', '37'])).
% 0.97/1.20  thf('39', plain,
% 0.97/1.20      (![X19 : $i, X21 : $i]:
% 0.97/1.20         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.97/1.20      inference('cnf', [status(esa)], [t3_subset])).
% 0.97/1.20  thf('40', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.20         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['38', '39'])).
% 0.97/1.20  thf('41', plain,
% 0.97/1.20      (![X26 : $i, X27 : $i]:
% 0.97/1.20         (~ (l1_pre_topc @ X26)
% 0.97/1.20          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.97/1.20          | (m1_subset_1 @ (k1_tops_1 @ X26 @ X27) @ 
% 0.97/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ X26))))),
% 0.97/1.20      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.97/1.20  thf('42', plain,
% 0.97/1.20      ((((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.97/1.20          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20         | ~ (l1_pre_topc @ sk_A))) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['40', '41'])).
% 0.97/1.20  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('44', plain,
% 0.97/1.20      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.97/1.20         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.20         <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('demod', [status(thm)], ['42', '43'])).
% 0.97/1.20  thf('45', plain,
% 0.97/1.20      (((r1_tarski @ sk_D @ sk_C)) | 
% 0.97/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('split', [status(esa)], ['32'])).
% 0.97/1.20  thf('46', plain, (((r1_tarski @ sk_D @ sk_C))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '45'])).
% 0.97/1.20  thf('47', plain,
% 0.97/1.20      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_D) @ 
% 0.97/1.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 0.97/1.20  thf(t48_tops_1, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( l1_pre_topc @ A ) =>
% 0.97/1.20       ( ![B:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20           ( ![C:$i]:
% 0.97/1.20             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20               ( ( r1_tarski @ B @ C ) =>
% 0.97/1.20                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.97/1.20  thf('48', plain,
% 0.97/1.20      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.97/1.20          | ~ (r1_tarski @ X34 @ X36)
% 0.97/1.20          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ (k1_tops_1 @ X35 @ X36))
% 0.97/1.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 0.97/1.20          | ~ (l1_pre_topc @ X35))),
% 0.97/1.20      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.97/1.20  thf('49', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         (~ (l1_pre_topc @ sk_A)
% 0.97/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_D)) @ 
% 0.97/1.20             (k1_tops_1 @ sk_A @ X0))
% 0.97/1.20          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ X0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['47', '48'])).
% 0.97/1.20  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('51', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_D)) @ 
% 0.97/1.20             (k1_tops_1 @ sk_A @ X0))
% 0.97/1.20          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ X0))),
% 0.97/1.20      inference('demod', [status(thm)], ['49', '50'])).
% 0.97/1.20  thf('52', plain,
% 0.97/1.20      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_C)
% 0.97/1.20        | (r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_D)) @ 
% 0.97/1.20           (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['28', '51'])).
% 0.97/1.20  thf('53', plain,
% 0.97/1.20      (((r1_tarski @ sk_D @ sk_C)) <= (((r1_tarski @ sk_D @ sk_C)))),
% 0.97/1.20      inference('split', [status(esa)], ['32'])).
% 0.97/1.20  thf('54', plain, (((r1_tarski @ sk_D @ sk_C))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '45'])).
% 0.97/1.20  thf('55', plain, ((r1_tarski @ sk_D @ sk_C)),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.97/1.20  thf('56', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('57', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('split', [status(esa)], ['56'])).
% 0.97/1.20  thf('58', plain,
% 0.97/1.20      (![X32 : $i, X33 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 0.97/1.20          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 0.97/1.20          | ~ (l1_pre_topc @ X33))),
% 0.97/1.20      inference('cnf', [status(esa)], [t44_tops_1])).
% 0.97/1.20  thf('59', plain,
% 0.97/1.20      (((~ (l1_pre_topc @ sk_A)
% 0.97/1.20         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D)))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('sup-', [status(thm)], ['57', '58'])).
% 0.97/1.20  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('61', plain,
% 0.97/1.20      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('demod', [status(thm)], ['59', '60'])).
% 0.97/1.20  thf('62', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 0.97/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('split', [status(esa)], ['56'])).
% 0.97/1.20  thf('63', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '62'])).
% 0.97/1.20  thf('64', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D)),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.97/1.20  thf(t1_xboole_1, axiom,
% 0.97/1.20    (![A:$i,B:$i,C:$i]:
% 0.97/1.20     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.97/1.20       ( r1_tarski @ A @ C ) ))).
% 0.97/1.20  thf('65', plain,
% 0.97/1.20      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.97/1.20         (~ (r1_tarski @ X8 @ X9)
% 0.97/1.20          | ~ (r1_tarski @ X9 @ X10)
% 0.97/1.20          | (r1_tarski @ X8 @ X10))),
% 0.97/1.20      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.97/1.20  thf('66', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ X0)
% 0.97/1.20          | ~ (r1_tarski @ sk_D @ X0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['64', '65'])).
% 0.97/1.20  thf('67', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_C)),
% 0.97/1.20      inference('sup-', [status(thm)], ['55', '66'])).
% 0.97/1.20  thf('68', plain,
% 0.97/1.20      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k1_tops_1 @ sk_A @ sk_D)) @ 
% 0.97/1.20        (k1_tops_1 @ sk_A @ sk_C))),
% 0.97/1.20      inference('demod', [status(thm)], ['52', '67'])).
% 0.97/1.20  thf('69', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D)),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['61', '63'])).
% 0.97/1.20  thf(d10_xboole_0, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.97/1.20  thf('70', plain,
% 0.97/1.20      (![X0 : $i, X2 : $i]:
% 0.97/1.20         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.97/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.20  thf('71', plain,
% 0.97/1.20      ((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_D))
% 0.97/1.20        | ((sk_D) = (k1_tops_1 @ sk_A @ sk_D)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['69', '70'])).
% 0.97/1.20  thf('72', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.97/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.97/1.20  thf('73', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.20      inference('simplify', [status(thm)], ['72'])).
% 0.97/1.20  thf('74', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('split', [status(esa)], ['56'])).
% 0.97/1.20  thf('75', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '62'])).
% 0.97/1.20  thf('76', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.97/1.20  thf(t35_subset_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.97/1.20       ( ![C:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.97/1.20           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.97/1.20             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.97/1.20  thf('77', plain,
% 0.97/1.20      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.97/1.20          | (r1_tarski @ X16 @ (k3_subset_1 @ X17 @ X18))
% 0.97/1.20          | ~ (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.97/1.20          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.97/1.20      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.97/1.20  thf('78', plain,
% 0.97/1.20      (![X0 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.97/1.20          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.97/1.20          | (r1_tarski @ sk_D @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['76', '77'])).
% 0.97/1.20  thf('79', plain,
% 0.97/1.20      (((r1_tarski @ sk_D @ 
% 0.97/1.20         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.97/1.20          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 0.97/1.20        | ~ (m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.97/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.97/1.20      inference('sup-', [status(thm)], ['73', '78'])).
% 0.97/1.20  thf('80', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('split', [status(esa)], ['56'])).
% 0.97/1.20  thf(d1_tops_1, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( l1_pre_topc @ A ) =>
% 0.97/1.20       ( ![B:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20           ( ( k1_tops_1 @ A @ B ) =
% 0.97/1.20             ( k3_subset_1 @
% 0.97/1.20               ( u1_struct_0 @ A ) @ 
% 0.97/1.20               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.97/1.20  thf('81', plain,
% 0.97/1.20      (![X24 : $i, X25 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.97/1.20          | ((k1_tops_1 @ X25 @ X24)
% 0.97/1.20              = (k3_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.97/1.20                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 0.97/1.20          | ~ (l1_pre_topc @ X25))),
% 0.97/1.20      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.97/1.20  thf('82', plain,
% 0.97/1.20      (((~ (l1_pre_topc @ sk_A)
% 0.97/1.20         | ((k1_tops_1 @ sk_A @ sk_D)
% 0.97/1.20             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.97/1.20                (k2_pre_topc @ sk_A @ 
% 0.97/1.20                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('sup-', [status(thm)], ['80', '81'])).
% 0.97/1.20  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('84', plain,
% 0.97/1.20      ((((k1_tops_1 @ sk_A @ sk_D)
% 0.97/1.20          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.97/1.20             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('demod', [status(thm)], ['82', '83'])).
% 0.97/1.20  thf('85', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '62'])).
% 0.97/1.20  thf('86', plain,
% 0.97/1.20      (((k1_tops_1 @ sk_A @ sk_D)
% 0.97/1.20         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.97/1.20            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['84', '85'])).
% 0.97/1.20  thf('87', plain,
% 0.97/1.20      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['74', '75'])).
% 0.97/1.20  thf(dt_k3_subset_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.97/1.20       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.97/1.20  thf('88', plain,
% 0.97/1.20      (![X14 : $i, X15 : $i]:
% 0.97/1.20         ((m1_subset_1 @ (k3_subset_1 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 0.97/1.20          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 0.97/1.20      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.97/1.20  thf('89', plain,
% 0.97/1.20      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.97/1.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 0.97/1.20  thf(t52_pre_topc, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( l1_pre_topc @ A ) =>
% 0.97/1.20       ( ![B:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.97/1.20             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.97/1.20               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.97/1.20  thf('90', plain,
% 0.97/1.20      (![X22 : $i, X23 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.97/1.20          | ~ (v4_pre_topc @ X22 @ X23)
% 0.97/1.20          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.97/1.20          | ~ (l1_pre_topc @ X23))),
% 0.97/1.20      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.97/1.20  thf('91', plain,
% 0.97/1.20      ((~ (l1_pre_topc @ sk_A)
% 0.97/1.20        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.97/1.20            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.97/1.20        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))),
% 0.97/1.20      inference('sup-', [status(thm)], ['89', '90'])).
% 0.97/1.20  thf('92', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('93', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('split', [status(esa)], ['56'])).
% 0.97/1.20  thf(t30_tops_1, axiom,
% 0.97/1.20    (![A:$i]:
% 0.97/1.20     ( ( l1_pre_topc @ A ) =>
% 0.97/1.20       ( ![B:$i]:
% 0.97/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.97/1.20           ( ( v3_pre_topc @ B @ A ) <=>
% 0.97/1.20             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.97/1.20  thf('94', plain,
% 0.97/1.20      (![X30 : $i, X31 : $i]:
% 0.97/1.20         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.97/1.20          | ~ (v3_pre_topc @ X30 @ X31)
% 0.97/1.20          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X31) @ X30) @ X31)
% 0.97/1.20          | ~ (l1_pre_topc @ X31))),
% 0.97/1.20      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.97/1.20  thf('95', plain,
% 0.97/1.20      (((~ (l1_pre_topc @ sk_A)
% 0.97/1.20         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.97/1.20         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('sup-', [status(thm)], ['93', '94'])).
% 0.97/1.20  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('97', plain,
% 0.97/1.20      ((((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 0.97/1.20         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('demod', [status(thm)], ['95', '96'])).
% 0.97/1.20  thf('98', plain,
% 0.97/1.20      (((v3_pre_topc @ sk_D @ sk_A)
% 0.97/1.20        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.97/1.20  thf('99', plain,
% 0.97/1.20      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 0.97/1.20      inference('split', [status(esa)], ['98'])).
% 0.97/1.20  thf('100', plain,
% 0.97/1.20      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 0.97/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('split', [status(esa)], ['98'])).
% 0.97/1.20  thf('101', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '100'])).
% 0.97/1.20  thf('102', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['99', '101'])).
% 0.97/1.20  thf('103', plain,
% 0.97/1.20      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))
% 0.97/1.20         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 0.97/1.20      inference('demod', [status(thm)], ['97', '102'])).
% 0.97/1.20  thf('104', plain,
% 0.97/1.20      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '62'])).
% 0.97/1.20  thf('105', plain,
% 0.97/1.20      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['103', '104'])).
% 0.97/1.20  thf('106', plain,
% 0.97/1.20      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 0.97/1.20         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 0.97/1.20      inference('demod', [status(thm)], ['91', '92', '105'])).
% 0.97/1.20  thf('107', plain,
% 0.97/1.20      (((k1_tops_1 @ sk_A @ sk_D)
% 0.97/1.20         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.97/1.20            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 0.97/1.20      inference('demod', [status(thm)], ['86', '106'])).
% 0.97/1.20  thf('108', plain,
% 0.97/1.20      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 0.97/1.20        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['87', '88'])).
% 0.97/1.20  thf('109', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_D))),
% 0.97/1.20      inference('demod', [status(thm)], ['79', '107', '108'])).
% 0.97/1.20  thf('110', plain, (((sk_D) = (k1_tops_1 @ sk_A @ sk_D))),
% 0.97/1.20      inference('demod', [status(thm)], ['71', '109'])).
% 0.97/1.20  thf('111', plain, (((sk_D) = (k1_tops_1 @ sk_A @ sk_D))),
% 0.97/1.20      inference('demod', [status(thm)], ['71', '109'])).
% 0.97/1.20  thf('112', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.97/1.20      inference('demod', [status(thm)], ['68', '110', '111'])).
% 0.97/1.20  thf('113', plain,
% 0.97/1.20      (![X6 : $i, X7 : $i]:
% 0.97/1.20         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.97/1.20      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.20  thf('114', plain,
% 0.97/1.20      (((k2_xboole_0 @ sk_D @ (k1_tops_1 @ sk_A @ sk_C))
% 0.97/1.20         = (k1_tops_1 @ sk_A @ sk_C))),
% 0.97/1.20      inference('sup-', [status(thm)], ['112', '113'])).
% 0.97/1.20  thf('115', plain,
% 0.97/1.20      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.97/1.20      inference('split', [status(esa)], ['3'])).
% 0.97/1.20  thf(l1_zfmisc_1, axiom,
% 0.97/1.20    (![A:$i,B:$i]:
% 0.97/1.20     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.97/1.20  thf('116', plain,
% 0.97/1.20      (![X11 : $i, X13 : $i]:
% 0.97/1.20         ((r1_tarski @ (k1_tarski @ X11) @ X13) | ~ (r2_hidden @ X11 @ X13))),
% 0.97/1.20      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.97/1.20  thf('117', plain,
% 0.97/1.20      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_D))
% 0.97/1.20         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['115', '116'])).
% 0.97/1.20  thf('118', plain,
% 0.97/1.20      (![X6 : $i, X7 : $i]:
% 0.97/1.20         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.97/1.20      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.97/1.20  thf('119', plain,
% 0.97/1.20      ((((k2_xboole_0 @ (k1_tarski @ sk_B) @ sk_D) = (sk_D)))
% 0.97/1.20         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['117', '118'])).
% 0.97/1.20  thf('120', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.97/1.20      inference('simplify', [status(thm)], ['72'])).
% 0.97/1.20  thf('121', plain,
% 0.97/1.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.20         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.97/1.20      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.20  thf('122', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['120', '121'])).
% 0.97/1.20  thf('123', plain,
% 0.97/1.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.97/1.20         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.97/1.20      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.97/1.20  thf('124', plain,
% 0.97/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.97/1.20         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.97/1.20      inference('sup-', [status(thm)], ['122', '123'])).
% 0.97/1.20  thf('125', plain,
% 0.97/1.20      ((![X0 : $i]:
% 0.97/1.20          (r1_tarski @ (k1_tarski @ sk_B) @ (k2_xboole_0 @ sk_D @ X0)))
% 0.97/1.20         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.97/1.20      inference('sup+', [status(thm)], ['119', '124'])).
% 0.97/1.20  thf('126', plain,
% 0.97/1.20      (![X11 : $i, X12 : $i]:
% 0.97/1.20         ((r2_hidden @ X11 @ X12) | ~ (r1_tarski @ (k1_tarski @ X11) @ X12))),
% 0.97/1.20      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.97/1.20  thf('127', plain,
% 0.97/1.20      ((![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_D @ X0)))
% 0.97/1.20         <= (((r2_hidden @ sk_B @ sk_D)))),
% 0.97/1.20      inference('sup-', [status(thm)], ['125', '126'])).
% 0.97/1.20  thf('128', plain,
% 0.97/1.20      (((r2_hidden @ sk_B @ sk_D)) | 
% 0.97/1.20       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)))),
% 0.97/1.20      inference('split', [status(esa)], ['3'])).
% 0.97/1.20  thf('129', plain, (((r2_hidden @ sk_B @ sk_D))),
% 0.97/1.20      inference('sat_resolution*', [status(thm)], ['2', '25', '128'])).
% 0.97/1.20  thf('130', plain,
% 0.97/1.20      (![X0 : $i]: (r2_hidden @ sk_B @ (k2_xboole_0 @ sk_D @ X0))),
% 0.97/1.20      inference('simpl_trail', [status(thm)], ['127', '129'])).
% 0.97/1.20  thf('131', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.97/1.20      inference('sup+', [status(thm)], ['114', '130'])).
% 0.97/1.20  thf('132', plain, ($false), inference('demod', [status(thm)], ['27', '131'])).
% 0.97/1.20  
% 0.97/1.20  % SZS output end Refutation
% 0.97/1.20  
% 0.97/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
