%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Qv8f9MayL

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:05 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 750 expanded)
%              Number of leaves         :   30 ( 205 expanded)
%              Depth                    :   20
%              Number of atoms          : 1270 (12778 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

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
    ! [X33: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X33 @ sk_A )
      | ~ ( r1_tarski @ X33 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X33 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
    | ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X33 @ sk_A )
        | ~ ( r1_tarski @ X33 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X33 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('5',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X33 @ sk_A )
        | ~ ( r1_tarski @ X33 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X33 ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X33 @ sk_A )
        | ~ ( r1_tarski @ X33 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X33 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X33 @ sk_A )
        | ~ ( r1_tarski @ X33 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X33 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X24 @ X25 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('19',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) )
   <= ! [X33: $i] :
        ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X33 @ sk_A )
        | ~ ( r1_tarski @ X33 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X33 ) ) ),
    inference(demod,[status(thm)],['16','22'])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      & ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X33 @ sk_A )
          | ~ ( r1_tarski @ X33 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X33 ) ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,
    ( ~ ! [X33: $i] :
          ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X33 @ sk_A )
          | ~ ( r1_tarski @ X33 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X33 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('29',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['8'])).

thf('30',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference('sat_resolution*',[status(thm)],['2','25','29'])).

thf('31',plain,(
    r2_hidden @ sk_B @ sk_D ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['33'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( r1_tarski @ X30 @ X32 )
      | ( r1_tarski @ ( k1_tops_1 @ X31 @ X30 ) @ ( k1_tops_1 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ~ ( l1_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['43'])).

thf('46',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','25','45'])).

thf('47',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['44','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['43'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_C_1 ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('58',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_D @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('63',plain,
    ( ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r1_tarski @ sk_D @ ( u1_struct_0 @ sk_A ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X29 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X29 @ X28 ) @ X28 )
      | ~ ( l1_pre_topc @ X29 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('68',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ) )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ sk_D @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','25','45'])).

thf('72',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ sk_D ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ~ ( r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_D ) )
    | ( sk_D
      = ( k1_tops_1 @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('78',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k3_subset_1 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ( r1_tarski @ sk_D @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( r1_tarski @ sk_D @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','79'])).

thf('81',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('82',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( ( k1_tops_1 @ X21 @ X20 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k2_pre_topc @ X21 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) ) ) )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('83',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('87',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('88',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('90',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

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

thf('91',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = X18 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('92',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['34','36'])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('95',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X27 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('96',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A )
    | ~ ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['98'])).

thf('100',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['98'])).

thf('101',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference('sat_resolution*',[status(thm)],['2','25','100'])).

thf('102',plain,(
    v3_pre_topc @ sk_D @ sk_A ),
    inference(simpl_trail,[status(thm)],['99','101'])).

thf('103',plain,(
    v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['96','97','102'])).

thf('104',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['92','93','103'])).

thf('105',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['85','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['2','25','35'])).

thf('107',plain,
    ( ( k1_tops_1 @ sk_A @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['88','89'])).

thf('109',plain,(
    r1_tarski @ sk_D @ ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['80','107','108'])).

thf('110',plain,
    ( sk_D
    = ( k1_tops_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['74','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','110'])).

thf('112',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['27','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2Qv8f9MayL
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:36:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.29/1.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.29/1.47  % Solved by: fo/fo7.sh
% 1.29/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.29/1.47  % done 2187 iterations in 1.014s
% 1.29/1.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.29/1.47  % SZS output start Refutation
% 1.29/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.29/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.29/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.29/1.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.29/1.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.29/1.47  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.29/1.47  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.29/1.47  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.29/1.47  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.29/1.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.29/1.47  thf(sk_B_type, type, sk_B: $i).
% 1.29/1.47  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.29/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.29/1.47  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.29/1.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.29/1.47  thf(sk_D_type, type, sk_D: $i).
% 1.29/1.47  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.29/1.47  thf(t54_tops_1, conjecture,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47       ( ![B:$i,C:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 1.29/1.47             ( ?[D:$i]:
% 1.29/1.47               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 1.29/1.47                 ( v3_pre_topc @ D @ A ) & 
% 1.29/1.47                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.29/1.47    (~( ![A:$i]:
% 1.29/1.47        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.29/1.47          ( ![B:$i,C:$i]:
% 1.29/1.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 1.29/1.47                ( ?[D:$i]:
% 1.29/1.47                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 1.29/1.47                    ( v3_pre_topc @ D @ A ) & 
% 1.29/1.47                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.29/1.47    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 1.29/1.47  thf('0', plain,
% 1.29/1.47      (![X33 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47          | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47          | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47          | ~ (r2_hidden @ sk_B @ X33)
% 1.29/1.47          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('1', plain,
% 1.29/1.47      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.29/1.47         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf('2', plain,
% 1.29/1.47      (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))) | 
% 1.29/1.47       (![X33 : $i]:
% 1.29/1.47          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47           | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47           | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47           | ~ (r2_hidden @ sk_B @ X33)))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf('3', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(t44_tops_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 1.29/1.47  thf('4', plain,
% 1.29/1.47      (![X28 : $i, X29 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.29/1.47          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 1.29/1.47          | ~ (l1_pre_topc @ X29))),
% 1.29/1.47      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.29/1.47  thf('5', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['3', '4'])).
% 1.29/1.47  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('7', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 1.29/1.47      inference('demod', [status(thm)], ['5', '6'])).
% 1.29/1.47  thf('8', plain,
% 1.29/1.47      (((r2_hidden @ sk_B @ sk_D)
% 1.29/1.47        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('9', plain,
% 1.29/1.47      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 1.29/1.47         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 1.29/1.47      inference('split', [status(esa)], ['8'])).
% 1.29/1.47  thf('10', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(dt_k1_tops_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( l1_pre_topc @ A ) & 
% 1.29/1.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.29/1.47       ( m1_subset_1 @
% 1.29/1.47         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.29/1.47  thf('11', plain,
% 1.29/1.47      (![X22 : $i, X23 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X22)
% 1.29/1.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.29/1.47          | (m1_subset_1 @ (k1_tops_1 @ X22 @ X23) @ 
% 1.29/1.47             (k1_zfmisc_1 @ (u1_struct_0 @ X22))))),
% 1.29/1.47      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 1.29/1.47  thf('12', plain,
% 1.29/1.47      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.29/1.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['10', '11'])).
% 1.29/1.47  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('14', plain,
% 1.29/1.47      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 1.29/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('demod', [status(thm)], ['12', '13'])).
% 1.29/1.47  thf('15', plain,
% 1.29/1.47      ((![X33 : $i]:
% 1.29/1.47          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47           | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47           | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47           | ~ (r2_hidden @ sk_B @ X33)))
% 1.29/1.47         <= ((![X33 : $i]:
% 1.29/1.47                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47                 | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47                 | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47                 | ~ (r2_hidden @ sk_B @ X33))))),
% 1.29/1.47      inference('split', [status(esa)], ['0'])).
% 1.29/1.47  thf('16', plain,
% 1.29/1.47      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.29/1.47         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 1.29/1.47         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 1.29/1.47         <= ((![X33 : $i]:
% 1.29/1.47                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47                 | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47                 | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47                 | ~ (r2_hidden @ sk_B @ X33))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['14', '15'])).
% 1.29/1.47  thf('17', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(fc9_tops_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.29/1.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.29/1.47       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 1.29/1.47  thf('18', plain,
% 1.29/1.47      (![X24 : $i, X25 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ X24)
% 1.29/1.47          | ~ (v2_pre_topc @ X24)
% 1.29/1.47          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 1.29/1.47          | (v3_pre_topc @ (k1_tops_1 @ X24 @ X25) @ X24))),
% 1.29/1.47      inference('cnf', [status(esa)], [fc9_tops_1])).
% 1.29/1.47  thf('19', plain,
% 1.29/1.47      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 1.29/1.47        | ~ (v2_pre_topc @ sk_A)
% 1.29/1.47        | ~ (l1_pre_topc @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['17', '18'])).
% 1.29/1.47  thf('20', plain, ((v2_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('22', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 1.29/1.47      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.29/1.47  thf('23', plain,
% 1.29/1.47      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.29/1.47         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)))
% 1.29/1.47         <= ((![X33 : $i]:
% 1.29/1.47                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47                 | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47                 | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47                 | ~ (r2_hidden @ sk_B @ X33))))),
% 1.29/1.47      inference('demod', [status(thm)], ['16', '22'])).
% 1.29/1.47  thf('24', plain,
% 1.29/1.47      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))
% 1.29/1.47         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))) & 
% 1.29/1.47             (![X33 : $i]:
% 1.29/1.47                (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47                 | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47                 | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47                 | ~ (r2_hidden @ sk_B @ X33))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['9', '23'])).
% 1.29/1.47  thf('25', plain,
% 1.29/1.47      (~
% 1.29/1.47       (![X33 : $i]:
% 1.29/1.47          (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47           | ~ (v3_pre_topc @ X33 @ sk_A)
% 1.29/1.47           | ~ (r1_tarski @ X33 @ sk_C_1)
% 1.29/1.47           | ~ (r2_hidden @ sk_B @ X33))) | 
% 1.29/1.47       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['7', '24'])).
% 1.29/1.47  thf('26', plain, (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 1.29/1.47  thf('27', plain, (~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 1.29/1.47  thf('28', plain,
% 1.29/1.47      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 1.29/1.47      inference('split', [status(esa)], ['8'])).
% 1.29/1.47  thf('29', plain,
% 1.29/1.47      (((r2_hidden @ sk_B @ sk_D)) | 
% 1.29/1.47       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('split', [status(esa)], ['8'])).
% 1.29/1.47  thf('30', plain, (((r2_hidden @ sk_B @ sk_D))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '29'])).
% 1.29/1.47  thf('31', plain, ((r2_hidden @ sk_B @ sk_D)),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 1.29/1.47  thf('32', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('33', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('34', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('split', [status(esa)], ['33'])).
% 1.29/1.47  thf('35', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 1.29/1.47       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('split', [status(esa)], ['33'])).
% 1.29/1.47  thf('36', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 1.29/1.47  thf('37', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 1.29/1.47  thf(t48_tops_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47           ( ![C:$i]:
% 1.29/1.47             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47               ( ( r1_tarski @ B @ C ) =>
% 1.29/1.47                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.29/1.47  thf('38', plain,
% 1.29/1.47      (![X30 : $i, X31 : $i, X32 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.29/1.47          | ~ (r1_tarski @ X30 @ X32)
% 1.29/1.47          | (r1_tarski @ (k1_tops_1 @ X31 @ X30) @ (k1_tops_1 @ X31 @ X32))
% 1.29/1.47          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.29/1.47          | ~ (l1_pre_topc @ X31))),
% 1.29/1.47      inference('cnf', [status(esa)], [t48_tops_1])).
% 1.29/1.47  thf('39', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (l1_pre_topc @ sk_A)
% 1.29/1.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 1.29/1.47          | ~ (r1_tarski @ sk_D @ X0))),
% 1.29/1.47      inference('sup-', [status(thm)], ['37', '38'])).
% 1.29/1.47  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('41', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 1.29/1.47          | ~ (r1_tarski @ sk_D @ X0))),
% 1.29/1.47      inference('demod', [status(thm)], ['39', '40'])).
% 1.29/1.47  thf('42', plain,
% 1.29/1.47      ((~ (r1_tarski @ sk_D @ sk_C_1)
% 1.29/1.47        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['32', '41'])).
% 1.29/1.47  thf('43', plain,
% 1.29/1.47      (((r1_tarski @ sk_D @ sk_C_1)
% 1.29/1.47        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('44', plain,
% 1.29/1.47      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('split', [status(esa)], ['43'])).
% 1.29/1.47  thf('45', plain,
% 1.29/1.47      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 1.29/1.47       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('split', [status(esa)], ['43'])).
% 1.29/1.47  thf('46', plain, (((r1_tarski @ sk_D @ sk_C_1))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '45'])).
% 1.29/1.47  thf('47', plain, ((r1_tarski @ sk_D @ sk_C_1)),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['44', '46'])).
% 1.29/1.47  thf('48', plain,
% 1.29/1.47      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.29/1.47      inference('demod', [status(thm)], ['42', '47'])).
% 1.29/1.47  thf(d3_tarski, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( r1_tarski @ A @ B ) <=>
% 1.29/1.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.29/1.47  thf('49', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X0 @ X1)
% 1.29/1.47          | (r2_hidden @ X0 @ X2)
% 1.29/1.47          | ~ (r1_tarski @ X1 @ X2))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('50', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.29/1.47          | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['48', '49'])).
% 1.29/1.47  thf('51', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('52', plain,
% 1.29/1.47      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('split', [status(esa)], ['43'])).
% 1.29/1.47  thf('53', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X0 @ X1)
% 1.29/1.47          | (r2_hidden @ X0 @ X2)
% 1.29/1.47          | ~ (r1_tarski @ X1 @ X2))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('54', plain,
% 1.29/1.47      ((![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_D)))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['52', '53'])).
% 1.29/1.47  thf('55', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_C_1)))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['51', '54'])).
% 1.29/1.47  thf('56', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf(t3_subset, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.29/1.47  thf('57', plain,
% 1.29/1.47      (![X15 : $i, X16 : $i]:
% 1.29/1.47         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t3_subset])).
% 1.29/1.47  thf('58', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['56', '57'])).
% 1.29/1.47  thf('59', plain,
% 1.29/1.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.29/1.47         (~ (r2_hidden @ X0 @ X1)
% 1.29/1.47          | (r2_hidden @ X0 @ X2)
% 1.29/1.47          | ~ (r1_tarski @ X1 @ X2))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('60', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['58', '59'])).
% 1.29/1.47  thf('61', plain,
% 1.29/1.47      ((![X0 : $i]:
% 1.29/1.47          ((r1_tarski @ sk_D @ X0)
% 1.29/1.47           | (r2_hidden @ (sk_C @ X0 @ sk_D) @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['55', '60'])).
% 1.29/1.47  thf('62', plain,
% 1.29/1.47      (![X1 : $i, X3 : $i]:
% 1.29/1.47         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.29/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.29/1.47  thf('63', plain,
% 1.29/1.47      ((((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))
% 1.29/1.47         | (r1_tarski @ sk_D @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['61', '62'])).
% 1.29/1.47  thf('64', plain,
% 1.29/1.47      (((r1_tarski @ sk_D @ (u1_struct_0 @ sk_A)))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('simplify', [status(thm)], ['63'])).
% 1.29/1.47  thf('65', plain,
% 1.29/1.47      (![X15 : $i, X17 : $i]:
% 1.29/1.47         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.29/1.47      inference('cnf', [status(esa)], [t3_subset])).
% 1.29/1.47  thf('66', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['64', '65'])).
% 1.29/1.47  thf('67', plain,
% 1.29/1.47      (![X28 : $i, X29 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X29)))
% 1.29/1.47          | (r1_tarski @ (k1_tops_1 @ X29 @ X28) @ X28)
% 1.29/1.47          | ~ (l1_pre_topc @ X29))),
% 1.29/1.47      inference('cnf', [status(esa)], [t44_tops_1])).
% 1.29/1.47  thf('68', plain,
% 1.29/1.47      (((~ (l1_pre_topc @ sk_A)
% 1.29/1.47         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D)))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['66', '67'])).
% 1.29/1.47  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('70', plain,
% 1.29/1.47      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D))
% 1.29/1.47         <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 1.29/1.47      inference('demod', [status(thm)], ['68', '69'])).
% 1.29/1.47  thf('71', plain, (((r1_tarski @ sk_D @ sk_C_1))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '45'])).
% 1.29/1.47  thf('72', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ sk_D)),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['70', '71'])).
% 1.29/1.47  thf(d10_xboole_0, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.29/1.47  thf('73', plain,
% 1.29/1.47      (![X4 : $i, X6 : $i]:
% 1.29/1.47         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.29/1.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.47  thf('74', plain,
% 1.29/1.47      ((~ (r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_D))
% 1.29/1.47        | ((sk_D) = (k1_tops_1 @ sk_A @ sk_D)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['72', '73'])).
% 1.29/1.47  thf('75', plain,
% 1.29/1.47      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 1.29/1.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.29/1.47  thf('76', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 1.29/1.47      inference('simplify', [status(thm)], ['75'])).
% 1.29/1.47  thf('77', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 1.29/1.47  thf(t35_subset_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.29/1.47       ( ![C:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.29/1.47           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 1.29/1.47             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 1.29/1.47  thf('78', plain,
% 1.29/1.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 1.29/1.47          | (r1_tarski @ X12 @ (k3_subset_1 @ X13 @ X14))
% 1.29/1.47          | ~ (r1_tarski @ X14 @ (k3_subset_1 @ X13 @ X12))
% 1.29/1.47          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 1.29/1.47      inference('cnf', [status(esa)], [t35_subset_1])).
% 1.29/1.47  thf('79', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.29/1.47          | ~ (r1_tarski @ X0 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.29/1.47          | (r1_tarski @ sk_D @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.29/1.47      inference('sup-', [status(thm)], ['77', '78'])).
% 1.29/1.47  thf('80', plain,
% 1.29/1.47      (((r1_tarski @ sk_D @ 
% 1.29/1.47         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 1.29/1.47        | ~ (m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 1.29/1.47             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['76', '79'])).
% 1.29/1.47  thf('81', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('split', [status(esa)], ['33'])).
% 1.29/1.47  thf(d1_tops_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47           ( ( k1_tops_1 @ A @ B ) =
% 1.29/1.47             ( k3_subset_1 @
% 1.29/1.47               ( u1_struct_0 @ A ) @ 
% 1.29/1.47               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.29/1.47  thf('82', plain,
% 1.29/1.47      (![X20 : $i, X21 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.29/1.47          | ((k1_tops_1 @ X21 @ X20)
% 1.29/1.47              = (k3_subset_1 @ (u1_struct_0 @ X21) @ 
% 1.29/1.47                 (k2_pre_topc @ X21 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20))))
% 1.29/1.47          | ~ (l1_pre_topc @ X21))),
% 1.29/1.47      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.29/1.47  thf('83', plain,
% 1.29/1.47      (((~ (l1_pre_topc @ sk_A)
% 1.29/1.47         | ((k1_tops_1 @ sk_A @ sk_D)
% 1.29/1.47             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47                (k2_pre_topc @ sk_A @ 
% 1.29/1.47                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['81', '82'])).
% 1.29/1.47  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('85', plain,
% 1.29/1.47      ((((k1_tops_1 @ sk_A @ sk_D)
% 1.29/1.47          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('demod', [status(thm)], ['83', '84'])).
% 1.29/1.47  thf('86', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('split', [status(esa)], ['33'])).
% 1.29/1.47  thf(dt_k3_subset_1, axiom,
% 1.29/1.47    (![A:$i,B:$i]:
% 1.29/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.29/1.47       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.29/1.47  thf('87', plain,
% 1.29/1.47      (![X10 : $i, X11 : $i]:
% 1.29/1.47         ((m1_subset_1 @ (k3_subset_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 1.29/1.47          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 1.29/1.47      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.29/1.47  thf('88', plain,
% 1.29/1.47      (((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 1.29/1.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('sup-', [status(thm)], ['86', '87'])).
% 1.29/1.47  thf('89', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 1.29/1.47  thf('90', plain,
% 1.29/1.47      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 1.29/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 1.29/1.47  thf(t52_pre_topc, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.29/1.47             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.29/1.47               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.29/1.47  thf('91', plain,
% 1.29/1.47      (![X18 : $i, X19 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.29/1.47          | ~ (v4_pre_topc @ X18 @ X19)
% 1.29/1.47          | ((k2_pre_topc @ X19 @ X18) = (X18))
% 1.29/1.47          | ~ (l1_pre_topc @ X19))),
% 1.29/1.47      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.29/1.47  thf('92', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.29/1.47            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.29/1.47        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['90', '91'])).
% 1.29/1.47  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('94', plain,
% 1.29/1.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['34', '36'])).
% 1.29/1.47  thf(t30_tops_1, axiom,
% 1.29/1.47    (![A:$i]:
% 1.29/1.47     ( ( l1_pre_topc @ A ) =>
% 1.29/1.47       ( ![B:$i]:
% 1.29/1.47         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.29/1.47           ( ( v3_pre_topc @ B @ A ) <=>
% 1.29/1.47             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.29/1.47  thf('95', plain,
% 1.29/1.47      (![X26 : $i, X27 : $i]:
% 1.29/1.47         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.29/1.47          | ~ (v3_pre_topc @ X26 @ X27)
% 1.29/1.47          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26) @ X27)
% 1.29/1.47          | ~ (l1_pre_topc @ X27))),
% 1.29/1.47      inference('cnf', [status(esa)], [t30_tops_1])).
% 1.29/1.47  thf('96', plain,
% 1.29/1.47      ((~ (l1_pre_topc @ sk_A)
% 1.29/1.47        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)
% 1.29/1.47        | ~ (v3_pre_topc @ sk_D @ sk_A))),
% 1.29/1.47      inference('sup-', [status(thm)], ['94', '95'])).
% 1.29/1.47  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('98', plain,
% 1.29/1.47      (((v3_pre_topc @ sk_D @ sk_A)
% 1.29/1.47        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.29/1.47  thf('99', plain,
% 1.29/1.47      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 1.29/1.47      inference('split', [status(esa)], ['98'])).
% 1.29/1.47  thf('100', plain,
% 1.29/1.47      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 1.29/1.47       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 1.29/1.47      inference('split', [status(esa)], ['98'])).
% 1.29/1.47  thf('101', plain, (((v3_pre_topc @ sk_D @ sk_A))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '100'])).
% 1.29/1.47  thf('102', plain, ((v3_pre_topc @ sk_D @ sk_A)),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['99', '101'])).
% 1.29/1.47  thf('103', plain,
% 1.29/1.47      ((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ sk_A)),
% 1.29/1.47      inference('demod', [status(thm)], ['96', '97', '102'])).
% 1.29/1.47  thf('104', plain,
% 1.29/1.47      (((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))
% 1.29/1.47         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))),
% 1.29/1.47      inference('demod', [status(thm)], ['92', '93', '103'])).
% 1.29/1.47  thf('105', plain,
% 1.29/1.47      ((((k1_tops_1 @ sk_A @ sk_D)
% 1.29/1.47          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 1.29/1.47         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 1.29/1.47      inference('demod', [status(thm)], ['85', '104'])).
% 1.29/1.47  thf('106', plain,
% 1.29/1.47      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.29/1.47      inference('sat_resolution*', [status(thm)], ['2', '25', '35'])).
% 1.29/1.47  thf('107', plain,
% 1.29/1.47      (((k1_tops_1 @ sk_A @ sk_D)
% 1.29/1.47         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.29/1.47            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['105', '106'])).
% 1.29/1.47  thf('108', plain,
% 1.29/1.47      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D) @ 
% 1.29/1.47        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.29/1.47      inference('simpl_trail', [status(thm)], ['88', '89'])).
% 1.29/1.47  thf('109', plain, ((r1_tarski @ sk_D @ (k1_tops_1 @ sk_A @ sk_D))),
% 1.29/1.47      inference('demod', [status(thm)], ['80', '107', '108'])).
% 1.29/1.47  thf('110', plain, (((sk_D) = (k1_tops_1 @ sk_A @ sk_D))),
% 1.29/1.47      inference('demod', [status(thm)], ['74', '109'])).
% 1.29/1.47  thf('111', plain,
% 1.29/1.47      (![X0 : $i]:
% 1.29/1.47         ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 1.29/1.47          | ~ (r2_hidden @ X0 @ sk_D))),
% 1.29/1.47      inference('demod', [status(thm)], ['50', '110'])).
% 1.29/1.47  thf('112', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))),
% 1.29/1.47      inference('sup-', [status(thm)], ['31', '111'])).
% 1.29/1.47  thf('113', plain, ($false), inference('demod', [status(thm)], ['27', '112'])).
% 1.29/1.47  
% 1.29/1.47  % SZS output end Refutation
% 1.29/1.47  
% 1.29/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
