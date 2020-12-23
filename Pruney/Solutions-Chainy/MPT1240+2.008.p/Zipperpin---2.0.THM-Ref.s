%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ED5hvDVQu

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:06 EST 2020

% Result     : Theorem 8.96s
% Output     : Refutation 8.96s
% Verified   : 
% Statistics : Number of formulae       :  264 (1523 expanded)
%              Number of leaves         :   57 ( 491 expanded)
%              Depth                    :   24
%              Number of atoms          : 2441 (15199 expanded)
%              Number of equality atoms :  126 ( 749 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X69: $i] :
      ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X69 @ sk_A )
      | ~ ( r1_tarski @ X69 @ sk_C_1 )
      | ~ ( r2_hidden @ sk_B @ X69 )
      | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X69: $i] :
        ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X69 @ sk_A )
        | ~ ( r1_tarski @ X69 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X69 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('10',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( l1_pre_topc @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X60 @ X61 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ! [X69: $i] :
        ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X69 @ sk_A )
        | ~ ( r1_tarski @ X69 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X69 ) )
   <= ! [X69: $i] :
        ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X69 @ sk_A )
        | ~ ( r1_tarski @ X69 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X69 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('15',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
      | ~ ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ) )
   <= ! [X69: $i] :
        ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X69 @ sk_A )
        | ~ ( r1_tarski @ X69 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X69 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('17',plain,(
    ! [X64: $i,X65: $i] :
      ( ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X65 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X65 @ X64 ) @ X64 )
      | ~ ( l1_pre_topc @ X65 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('22',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( l1_pre_topc @ X62 )
      | ~ ( v2_pre_topc @ X62 )
      | ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X62 @ X63 ) @ X62 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('23',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ! [X69: $i] :
        ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( v3_pre_topc @ X69 @ sk_A )
        | ~ ( r1_tarski @ X69 @ sk_C_1 )
        | ~ ( r2_hidden @ sk_B @ X69 ) ) ),
    inference(demod,[status(thm)],['15','20','26'])).

thf('28',plain,
    ( ~ ! [X69: $i] :
          ( ~ ( m1_subset_1 @ X69 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( v3_pre_topc @ X69 @ sk_A )
          | ~ ( r1_tarski @ X69 @ sk_C_1 )
          | ~ ( r2_hidden @ sk_B @ X69 ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','27'])).

thf('29',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_D )
   <= ( r2_hidden @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( v3_pre_topc @ sk_D @ sk_A )
   <= ( v3_pre_topc @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['29'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('34',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('35',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X55: $i] :
      ( ( l1_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t53_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) )
                  = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('41',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( v3_pre_topc @ X56 @ X57 )
      | ( ( k2_pre_topc @ X57 @ ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_struct_0 @ X57 ) @ X56 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_struct_0 @ X57 ) @ X56 ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t53_pre_topc])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('46',plain,
    ( ( ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('48',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('53',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) )
        = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ sk_C_1 ) )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('57',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('59',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('60',plain,(
    ! [X34: $i] :
      ( r1_tarski @ ( k1_tarski @ X34 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('63',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('68',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('72',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X26 != X25 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X25 ) )
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('73',plain,(
    ! [X25: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X25 ) @ ( k1_tarski @ X25 ) )
     != ( k1_tarski @ X25 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('74',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('77',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X25: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X25 ) ) ),
    inference(demod,[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['71','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','80'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('82',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( m1_subset_1 @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('84',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('86',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('91',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('92',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','58','87','90','95'])).

thf('97',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ sk_C_1 ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
      = ( k4_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('109',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('112',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('115',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('117',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('118',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['115','118'])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['102','105','106','107','108','119'])).

thf('121',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['97','120'])).

thf('122',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('123',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('126',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('129',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('130',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','123'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('133',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('134',plain,
    ( ( ~ ( v3_pre_topc @ sk_D @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','124','127','130','131','132','133'])).

thf('135',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','134'])).

thf('136',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('137',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('138',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ ( k2_pre_topc @ X59 @ ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 ) ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('142',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('143',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('144',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
        = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['141','144'])).

thf('146',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('147',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('149',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('152',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['140','149','150','151'])).

thf('153',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['96','123'])).

thf('154',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['135','154'])).

thf('156',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['83','84'])).

thf('158',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('159',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D ) )
          = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['157','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('163',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('164',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('165',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('167',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('168',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('169',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k4_subset_1 @ X42 @ X41 @ X43 )
        = ( k2_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('171',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('172',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('173',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X16 = X15 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( ( k2_xboole_0 @ X17 @ X15 )
       != ( k2_xboole_0 @ X16 @ X18 ) )
      | ~ ( r1_xboole_0 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('174',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('177',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('178',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_xboole_0 @ X19 @ ( k4_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['176','179'])).

thf('181',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['175','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['171','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['170','182'])).

thf('184',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_D )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['167','183'])).

thf('185',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['161','162','165','166','184'])).

thf('186',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = sk_D )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['156','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('188',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['155','188'])).

thf('190',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('191',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('193',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( r1_tarski @ X66 @ X68 )
      | ( r1_tarski @ ( k1_tops_1 @ X67 @ X66 ) @ ( k1_tops_1 @ X67 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('194',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['194','195'])).

thf('197',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['190','197'])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('200',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['189','200'])).

thf('202',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','201'])).

thf('203',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('204',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['202','203'])).

thf('205',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','28','30','204'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2ED5hvDVQu
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:38:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 8.96/9.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.96/9.13  % Solved by: fo/fo7.sh
% 8.96/9.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.96/9.13  % done 18760 iterations in 8.673s
% 8.96/9.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.96/9.13  % SZS output start Refutation
% 8.96/9.13  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.96/9.13  thf(sk_B_type, type, sk_B: $i).
% 8.96/9.13  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.96/9.13  thf(sk_D_type, type, sk_D: $i).
% 8.96/9.13  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 8.96/9.13  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.96/9.13  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.96/9.13  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.96/9.13  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.96/9.13  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.96/9.13  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.96/9.13  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.96/9.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.96/9.13  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.96/9.13  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.96/9.13  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.96/9.13  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.96/9.13  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 8.96/9.13  thf(sk_A_type, type, sk_A: $i).
% 8.96/9.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.96/9.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.96/9.13  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.96/9.13  thf(sk_C_1_type, type, sk_C_1: $i).
% 8.96/9.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.96/9.13  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.96/9.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.96/9.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.96/9.13  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.96/9.13  thf(t54_tops_1, conjecture,
% 8.96/9.13    (![A:$i]:
% 8.96/9.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.96/9.13       ( ![B:$i,C:$i]:
% 8.96/9.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 8.96/9.13             ( ?[D:$i]:
% 8.96/9.13               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 8.96/9.13                 ( v3_pre_topc @ D @ A ) & 
% 8.96/9.13                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 8.96/9.13  thf(zf_stmt_0, negated_conjecture,
% 8.96/9.13    (~( ![A:$i]:
% 8.96/9.13        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.96/9.13          ( ![B:$i,C:$i]:
% 8.96/9.13            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 8.96/9.13                ( ?[D:$i]:
% 8.96/9.13                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 8.96/9.13                    ( v3_pre_topc @ D @ A ) & 
% 8.96/9.13                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 8.96/9.13    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 8.96/9.13  thf('0', plain,
% 8.96/9.13      (((r2_hidden @ sk_B @ sk_D)
% 8.96/9.13        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('1', plain,
% 8.96/9.13      (((r2_hidden @ sk_B @ sk_D)) | 
% 8.96/9.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('split', [status(esa)], ['0'])).
% 8.96/9.13  thf('2', plain,
% 8.96/9.13      (((r1_tarski @ sk_D @ sk_C_1)
% 8.96/9.13        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('3', plain,
% 8.96/9.13      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 8.96/9.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('split', [status(esa)], ['2'])).
% 8.96/9.13  thf('4', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('5', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 8.96/9.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('split', [status(esa)], ['4'])).
% 8.96/9.13  thf('6', plain,
% 8.96/9.13      (![X69 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13          | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13          | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13          | ~ (r2_hidden @ sk_B @ X69)
% 8.96/9.13          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('7', plain,
% 8.96/9.13      ((![X69 : $i]:
% 8.96/9.13          (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13           | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13           | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13           | ~ (r2_hidden @ sk_B @ X69))) | 
% 8.96/9.13       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('split', [status(esa)], ['6'])).
% 8.96/9.13  thf('8', plain,
% 8.96/9.13      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 8.96/9.13         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 8.96/9.13      inference('split', [status(esa)], ['0'])).
% 8.96/9.13  thf('9', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf(dt_k1_tops_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( ( l1_pre_topc @ A ) & 
% 8.96/9.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.96/9.13       ( m1_subset_1 @
% 8.96/9.13         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.96/9.13  thf('10', plain,
% 8.96/9.13      (![X60 : $i, X61 : $i]:
% 8.96/9.13         (~ (l1_pre_topc @ X60)
% 8.96/9.13          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 8.96/9.13          | (m1_subset_1 @ (k1_tops_1 @ X60 @ X61) @ 
% 8.96/9.13             (k1_zfmisc_1 @ (u1_struct_0 @ X60))))),
% 8.96/9.13      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 8.96/9.13  thf('11', plain,
% 8.96/9.13      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 8.96/9.13         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13        | ~ (l1_pre_topc @ sk_A))),
% 8.96/9.13      inference('sup-', [status(thm)], ['9', '10'])).
% 8.96/9.13  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('13', plain,
% 8.96/9.13      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 8.96/9.13        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('demod', [status(thm)], ['11', '12'])).
% 8.96/9.13  thf('14', plain,
% 8.96/9.13      ((![X69 : $i]:
% 8.96/9.13          (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13           | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13           | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13           | ~ (r2_hidden @ sk_B @ X69)))
% 8.96/9.13         <= ((![X69 : $i]:
% 8.96/9.13                (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13                 | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13                 | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13                 | ~ (r2_hidden @ sk_B @ X69))))),
% 8.96/9.13      inference('split', [status(esa)], ['6'])).
% 8.96/9.13  thf('15', plain,
% 8.96/9.13      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 8.96/9.13         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 8.96/9.13         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 8.96/9.13         <= ((![X69 : $i]:
% 8.96/9.13                (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13                 | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13                 | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13                 | ~ (r2_hidden @ sk_B @ X69))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['13', '14'])).
% 8.96/9.13  thf('16', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf(t44_tops_1, axiom,
% 8.96/9.13    (![A:$i]:
% 8.96/9.13     ( ( l1_pre_topc @ A ) =>
% 8.96/9.13       ( ![B:$i]:
% 8.96/9.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 8.96/9.13  thf('17', plain,
% 8.96/9.13      (![X64 : $i, X65 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 8.96/9.13          | (r1_tarski @ (k1_tops_1 @ X65 @ X64) @ X64)
% 8.96/9.13          | ~ (l1_pre_topc @ X65))),
% 8.96/9.13      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.96/9.13  thf('18', plain,
% 8.96/9.13      ((~ (l1_pre_topc @ sk_A)
% 8.96/9.13        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['16', '17'])).
% 8.96/9.13  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 8.96/9.13      inference('demod', [status(thm)], ['18', '19'])).
% 8.96/9.13  thf('21', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf(fc9_tops_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 8.96/9.13         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.96/9.13       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 8.96/9.13  thf('22', plain,
% 8.96/9.13      (![X62 : $i, X63 : $i]:
% 8.96/9.13         (~ (l1_pre_topc @ X62)
% 8.96/9.13          | ~ (v2_pre_topc @ X62)
% 8.96/9.13          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 8.96/9.13          | (v3_pre_topc @ (k1_tops_1 @ X62 @ X63) @ X62))),
% 8.96/9.13      inference('cnf', [status(esa)], [fc9_tops_1])).
% 8.96/9.13  thf('23', plain,
% 8.96/9.13      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 8.96/9.13        | ~ (v2_pre_topc @ sk_A)
% 8.96/9.13        | ~ (l1_pre_topc @ sk_A))),
% 8.96/9.13      inference('sup-', [status(thm)], ['21', '22'])).
% 8.96/9.13  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('26', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 8.96/9.13      inference('demod', [status(thm)], ['23', '24', '25'])).
% 8.96/9.13  thf('27', plain,
% 8.96/9.13      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 8.96/9.13         <= ((![X69 : $i]:
% 8.96/9.13                (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13                 | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13                 | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13                 | ~ (r2_hidden @ sk_B @ X69))))),
% 8.96/9.13      inference('demod', [status(thm)], ['15', '20', '26'])).
% 8.96/9.13  thf('28', plain,
% 8.96/9.13      (~
% 8.96/9.13       (![X69 : $i]:
% 8.96/9.13          (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13           | ~ (v3_pre_topc @ X69 @ sk_A)
% 8.96/9.13           | ~ (r1_tarski @ X69 @ sk_C_1)
% 8.96/9.13           | ~ (r2_hidden @ sk_B @ X69))) | 
% 8.96/9.13       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['8', '27'])).
% 8.96/9.13  thf('29', plain,
% 8.96/9.13      (((v3_pre_topc @ sk_D @ sk_A)
% 8.96/9.13        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('30', plain,
% 8.96/9.13      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 8.96/9.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('split', [status(esa)], ['29'])).
% 8.96/9.13  thf('31', plain,
% 8.96/9.13      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 8.96/9.13      inference('split', [status(esa)], ['0'])).
% 8.96/9.13  thf('32', plain,
% 8.96/9.13      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 8.96/9.13      inference('split', [status(esa)], ['29'])).
% 8.96/9.13  thf(d3_struct_0, axiom,
% 8.96/9.13    (![A:$i]:
% 8.96/9.13     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 8.96/9.13  thf('33', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf('34', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('split', [status(esa)], ['4'])).
% 8.96/9.13  thf('35', plain,
% 8.96/9.13      ((((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.96/9.13         | ~ (l1_struct_0 @ sk_A)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['33', '34'])).
% 8.96/9.13  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf(dt_l1_pre_topc, axiom,
% 8.96/9.13    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 8.96/9.13  thf('37', plain,
% 8.96/9.13      (![X55 : $i]: ((l1_struct_0 @ X55) | ~ (l1_pre_topc @ X55))),
% 8.96/9.13      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 8.96/9.13  thf('38', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('39', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['35', '38'])).
% 8.96/9.13  thf('40', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf(t53_pre_topc, axiom,
% 8.96/9.13    (![A:$i]:
% 8.96/9.13     ( ( l1_pre_topc @ A ) =>
% 8.96/9.13       ( ![B:$i]:
% 8.96/9.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13           ( ( ( v3_pre_topc @ B @ A ) =>
% 8.96/9.13               ( ( k2_pre_topc @
% 8.96/9.13                   A @ 
% 8.96/9.13                   ( k7_subset_1 @
% 8.96/9.13                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 8.96/9.13                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 8.96/9.13             ( ( ( v2_pre_topc @ A ) & 
% 8.96/9.13                 ( ( k2_pre_topc @
% 8.96/9.13                     A @ 
% 8.96/9.13                     ( k7_subset_1 @
% 8.96/9.13                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 8.96/9.13                   ( k7_subset_1 @
% 8.96/9.13                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 8.96/9.13               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 8.96/9.13  thf('41', plain,
% 8.96/9.13      (![X56 : $i, X57 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 8.96/9.13          | ~ (v3_pre_topc @ X56 @ X57)
% 8.96/9.13          | ((k2_pre_topc @ X57 @ 
% 8.96/9.13              (k7_subset_1 @ (u1_struct_0 @ X57) @ (k2_struct_0 @ X57) @ X56))
% 8.96/9.13              = (k7_subset_1 @ (u1_struct_0 @ X57) @ (k2_struct_0 @ X57) @ X56))
% 8.96/9.13          | ~ (l1_pre_topc @ X57))),
% 8.96/9.13      inference('cnf', [status(esa)], [t53_pre_topc])).
% 8.96/9.13  thf('42', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 8.96/9.13          | ~ (l1_struct_0 @ X0)
% 8.96/9.13          | ~ (l1_pre_topc @ X0)
% 8.96/9.13          | ((k2_pre_topc @ X0 @ 
% 8.96/9.13              (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1))
% 8.96/9.13              = (k7_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1))
% 8.96/9.13          | ~ (v3_pre_topc @ X1 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['40', '41'])).
% 8.96/9.13  thf('43', plain,
% 8.96/9.13      (((~ (v3_pre_topc @ sk_D @ sk_A)
% 8.96/9.13         | ((k2_pre_topc @ sk_A @ 
% 8.96/9.13             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 8.96/9.13             = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13                sk_D))
% 8.96/9.13         | ~ (l1_pre_topc @ sk_A)
% 8.96/9.13         | ~ (l1_struct_0 @ sk_A)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['39', '42'])).
% 8.96/9.13  thf('44', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('45', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('46', plain,
% 8.96/9.13      (((~ (v3_pre_topc @ sk_D @ sk_A)
% 8.96/9.13         | ((k2_pre_topc @ sk_A @ 
% 8.96/9.13             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 8.96/9.13             = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13                sk_D))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['43', '44', '45'])).
% 8.96/9.13  thf('47', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf('48', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('49', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.96/9.13        | ~ (l1_struct_0 @ sk_A))),
% 8.96/9.13      inference('sup+', [status(thm)], ['47', '48'])).
% 8.96/9.13  thf('50', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('51', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 8.96/9.13      inference('demod', [status(thm)], ['49', '50'])).
% 8.96/9.13  thf('52', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 8.96/9.13      inference('demod', [status(thm)], ['49', '50'])).
% 8.96/9.13  thf(t33_subset_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.96/9.13       ( ![C:$i]:
% 8.96/9.13         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 8.96/9.13           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 8.96/9.13             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 8.96/9.13  thf('53', plain,
% 8.96/9.13      (![X47 : $i, X48 : $i, X49 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 8.96/9.13          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 8.96/9.13              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 8.96/9.13          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 8.96/9.13      inference('cnf', [status(esa)], [t33_subset_1])).
% 8.96/9.13  thf('54', plain,
% 8.96/9.13      (![X0 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 8.96/9.13          | ((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13              (k7_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1))
% 8.96/9.13              = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13                 (k3_subset_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_C_1)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['52', '53'])).
% 8.96/9.13  thf('55', plain,
% 8.96/9.13      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13         (k7_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ sk_C_1))
% 8.96/9.13         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['51', '54'])).
% 8.96/9.13  thf('56', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 8.96/9.13      inference('demod', [status(thm)], ['49', '50'])).
% 8.96/9.13  thf(redefinition_k7_subset_1, axiom,
% 8.96/9.13    (![A:$i,B:$i,C:$i]:
% 8.96/9.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.96/9.13       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.96/9.13  thf('57', plain,
% 8.96/9.13      (![X44 : $i, X45 : $i, X46 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 8.96/9.13          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 8.96/9.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.96/9.13  thf('58', plain,
% 8.96/9.13      (![X0 : $i]:
% 8.96/9.13         ((k7_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 8.96/9.13           = (k4_xboole_0 @ sk_C_1 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['56', '57'])).
% 8.96/9.13  thf(t69_enumset1, axiom,
% 8.96/9.13    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 8.96/9.13  thf('59', plain,
% 8.96/9.13      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 8.96/9.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.96/9.13  thf(t80_zfmisc_1, axiom,
% 8.96/9.13    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 8.96/9.13  thf('60', plain,
% 8.96/9.13      (![X34 : $i]: (r1_tarski @ (k1_tarski @ X34) @ (k1_zfmisc_1 @ X34))),
% 8.96/9.13      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 8.96/9.13  thf('61', plain,
% 8.96/9.13      (![X0 : $i]: (r1_tarski @ (k2_tarski @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['59', '60'])).
% 8.96/9.13  thf('62', plain,
% 8.96/9.13      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 8.96/9.13      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.96/9.13  thf(t56_zfmisc_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 8.96/9.13  thf('63', plain,
% 8.96/9.13      (![X32 : $i, X33 : $i]:
% 8.96/9.13         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 8.96/9.13      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 8.96/9.13  thf(d3_tarski, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( r1_tarski @ A @ B ) <=>
% 8.96/9.13       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.96/9.13  thf('64', plain,
% 8.96/9.13      (![X1 : $i, X3 : $i]:
% 8.96/9.13         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_tarski])).
% 8.96/9.13  thf('65', plain,
% 8.96/9.13      (![X1 : $i, X3 : $i]:
% 8.96/9.13         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_tarski])).
% 8.96/9.13  thf('66', plain,
% 8.96/9.13      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['64', '65'])).
% 8.96/9.13  thf('67', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.96/9.13      inference('simplify', [status(thm)], ['66'])).
% 8.96/9.13  thf(t67_xboole_1, axiom,
% 8.96/9.13    (![A:$i,B:$i,C:$i]:
% 8.96/9.13     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 8.96/9.13         ( r1_xboole_0 @ B @ C ) ) =>
% 8.96/9.13       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.96/9.13  thf('68', plain,
% 8.96/9.13      (![X12 : $i, X13 : $i, X14 : $i]:
% 8.96/9.13         (((X12) = (k1_xboole_0))
% 8.96/9.13          | ~ (r1_tarski @ X12 @ X13)
% 8.96/9.13          | ~ (r1_tarski @ X12 @ X14)
% 8.96/9.13          | ~ (r1_xboole_0 @ X13 @ X14))),
% 8.96/9.13      inference('cnf', [status(esa)], [t67_xboole_1])).
% 8.96/9.13  thf('69', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         (~ (r1_xboole_0 @ X0 @ X1)
% 8.96/9.13          | ~ (r1_tarski @ X0 @ X1)
% 8.96/9.13          | ((X0) = (k1_xboole_0)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['67', '68'])).
% 8.96/9.13  thf('70', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         ((r2_hidden @ X1 @ X0)
% 8.96/9.13          | ((k1_tarski @ X1) = (k1_xboole_0))
% 8.96/9.13          | ~ (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['63', '69'])).
% 8.96/9.13  thf('71', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         (~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1)
% 8.96/9.13          | ((k1_tarski @ X0) = (k1_xboole_0))
% 8.96/9.13          | (r2_hidden @ X0 @ X1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['62', '70'])).
% 8.96/9.13  thf(t20_zfmisc_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 8.96/9.13         ( k1_tarski @ A ) ) <=>
% 8.96/9.13       ( ( A ) != ( B ) ) ))).
% 8.96/9.13  thf('72', plain,
% 8.96/9.13      (![X25 : $i, X26 : $i]:
% 8.96/9.13         (((X26) != (X25))
% 8.96/9.13          | ((k4_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X25))
% 8.96/9.13              != (k1_tarski @ X26)))),
% 8.96/9.13      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 8.96/9.13  thf('73', plain,
% 8.96/9.13      (![X25 : $i]:
% 8.96/9.13         ((k4_xboole_0 @ (k1_tarski @ X25) @ (k1_tarski @ X25))
% 8.96/9.13           != (k1_tarski @ X25))),
% 8.96/9.13      inference('simplify', [status(thm)], ['72'])).
% 8.96/9.13  thf(t3_boole, axiom,
% 8.96/9.13    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.96/9.13  thf('74', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 8.96/9.13      inference('cnf', [status(esa)], [t3_boole])).
% 8.96/9.13  thf(t48_xboole_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.96/9.13  thf('75', plain,
% 8.96/9.13      (![X9 : $i, X10 : $i]:
% 8.96/9.13         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 8.96/9.13           = (k3_xboole_0 @ X9 @ X10))),
% 8.96/9.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 8.96/9.13  thf('76', plain,
% 8.96/9.13      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['74', '75'])).
% 8.96/9.13  thf(t2_boole, axiom,
% 8.96/9.13    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 8.96/9.13  thf('77', plain,
% 8.96/9.13      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 8.96/9.13      inference('cnf', [status(esa)], [t2_boole])).
% 8.96/9.13  thf('78', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.96/9.13      inference('demod', [status(thm)], ['76', '77'])).
% 8.96/9.13  thf('79', plain, (![X25 : $i]: ((k1_xboole_0) != (k1_tarski @ X25))),
% 8.96/9.13      inference('demod', [status(thm)], ['73', '78'])).
% 8.96/9.13  thf('80', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         ((r2_hidden @ X0 @ X1) | ~ (r1_tarski @ (k2_tarski @ X0 @ X0) @ X1))),
% 8.96/9.13      inference('clc', [status(thm)], ['71', '79'])).
% 8.96/9.13  thf('81', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['61', '80'])).
% 8.96/9.13  thf(d2_subset_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( ( v1_xboole_0 @ A ) =>
% 8.96/9.13         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 8.96/9.13       ( ( ~( v1_xboole_0 @ A ) ) =>
% 8.96/9.13         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 8.96/9.13  thf('82', plain,
% 8.96/9.13      (![X35 : $i, X36 : $i]:
% 8.96/9.13         (~ (r2_hidden @ X35 @ X36)
% 8.96/9.13          | (m1_subset_1 @ X35 @ X36)
% 8.96/9.13          | (v1_xboole_0 @ X36))),
% 8.96/9.13      inference('cnf', [status(esa)], [d2_subset_1])).
% 8.96/9.13  thf('83', plain,
% 8.96/9.13      (![X0 : $i]:
% 8.96/9.13         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 8.96/9.13          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['81', '82'])).
% 8.96/9.13  thf(fc1_subset_1, axiom,
% 8.96/9.13    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.96/9.13  thf('84', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 8.96/9.13      inference('cnf', [status(esa)], [fc1_subset_1])).
% 8.96/9.13  thf('85', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.96/9.13      inference('clc', [status(thm)], ['83', '84'])).
% 8.96/9.13  thf(d5_subset_1, axiom,
% 8.96/9.13    (![A:$i,B:$i]:
% 8.96/9.13     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.96/9.13       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.96/9.13  thf('86', plain,
% 8.96/9.13      (![X38 : $i, X39 : $i]:
% 8.96/9.13         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 8.96/9.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 8.96/9.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.96/9.13  thf('87', plain,
% 8.96/9.13      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['85', '86'])).
% 8.96/9.13  thf('88', plain,
% 8.96/9.13      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['85', '86'])).
% 8.96/9.13  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 8.96/9.13      inference('demod', [status(thm)], ['76', '77'])).
% 8.96/9.13  thf('90', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['88', '89'])).
% 8.96/9.13  thf(t4_subset_1, axiom,
% 8.96/9.13    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 8.96/9.13  thf('91', plain,
% 8.96/9.13      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 8.96/9.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.96/9.13  thf('92', plain,
% 8.96/9.13      (![X38 : $i, X39 : $i]:
% 8.96/9.13         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 8.96/9.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 8.96/9.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.96/9.13  thf('93', plain,
% 8.96/9.13      (![X0 : $i]:
% 8.96/9.13         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['91', '92'])).
% 8.96/9.13  thf('94', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 8.96/9.13      inference('cnf', [status(esa)], [t3_boole])).
% 8.96/9.13  thf('95', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['93', '94'])).
% 8.96/9.13  thf('96', plain,
% 8.96/9.13      (((k2_struct_0 @ sk_A)
% 8.96/9.13         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 8.96/9.13      inference('demod', [status(thm)], ['55', '58', '87', '90', '95'])).
% 8.96/9.13  thf('97', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf('98', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('99', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('100', plain,
% 8.96/9.13      (![X47 : $i, X48 : $i, X49 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 8.96/9.13          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 8.96/9.13              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 8.96/9.13          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 8.96/9.13      inference('cnf', [status(esa)], [t33_subset_1])).
% 8.96/9.13  thf('101', plain,
% 8.96/9.13      (![X0 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1))
% 8.96/9.13              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_C_1)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['99', '100'])).
% 8.96/9.13  thf('102', plain,
% 8.96/9.13      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ sk_C_1))
% 8.96/9.13         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['98', '101'])).
% 8.96/9.13  thf('103', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('104', plain,
% 8.96/9.13      (![X44 : $i, X45 : $i, X46 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 8.96/9.13          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 8.96/9.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.96/9.13  thf('105', plain,
% 8.96/9.13      (![X0 : $i]:
% 8.96/9.13         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 8.96/9.13           = (k4_xboole_0 @ sk_C_1 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['103', '104'])).
% 8.96/9.13  thf('106', plain,
% 8.96/9.13      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['85', '86'])).
% 8.96/9.13  thf('107', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['88', '89'])).
% 8.96/9.13  thf('108', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['93', '94'])).
% 8.96/9.13  thf('109', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf('110', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('111', plain,
% 8.96/9.13      (![X38 : $i, X39 : $i]:
% 8.96/9.13         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 8.96/9.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 8.96/9.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.96/9.13  thf('112', plain,
% 8.96/9.13      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 8.96/9.13         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['110', '111'])).
% 8.96/9.13  thf('113', plain,
% 8.96/9.13      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 8.96/9.13          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))
% 8.96/9.13        | ~ (l1_struct_0 @ sk_A))),
% 8.96/9.13      inference('sup+', [status(thm)], ['109', '112'])).
% 8.96/9.13  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('115', plain,
% 8.96/9.13      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)
% 8.96/9.13         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 8.96/9.13      inference('demod', [status(thm)], ['113', '114'])).
% 8.96/9.13  thf('116', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 8.96/9.13      inference('demod', [status(thm)], ['49', '50'])).
% 8.96/9.13  thf('117', plain,
% 8.96/9.13      (![X38 : $i, X39 : $i]:
% 8.96/9.13         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 8.96/9.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 8.96/9.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.96/9.13  thf('118', plain,
% 8.96/9.13      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1)
% 8.96/9.13         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['116', '117'])).
% 8.96/9.13  thf('119', plain,
% 8.96/9.13      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1)
% 8.96/9.13         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 8.96/9.13      inference('sup+', [status(thm)], ['115', '118'])).
% 8.96/9.13  thf('120', plain,
% 8.96/9.13      (((u1_struct_0 @ sk_A)
% 8.96/9.13         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 8.96/9.13      inference('demod', [status(thm)],
% 8.96/9.13                ['102', '105', '106', '107', '108', '119'])).
% 8.96/9.13  thf('121', plain,
% 8.96/9.13      ((((u1_struct_0 @ sk_A)
% 8.96/9.13          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))
% 8.96/9.13        | ~ (l1_struct_0 @ sk_A))),
% 8.96/9.13      inference('sup+', [status(thm)], ['97', '120'])).
% 8.96/9.13  thf('122', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('123', plain,
% 8.96/9.13      (((u1_struct_0 @ sk_A)
% 8.96/9.13         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_C_1) @ sk_C_1))),
% 8.96/9.13      inference('demod', [status(thm)], ['121', '122'])).
% 8.96/9.13  thf('124', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 8.96/9.13      inference('sup+', [status(thm)], ['96', '123'])).
% 8.96/9.13  thf('125', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.96/9.13      inference('clc', [status(thm)], ['83', '84'])).
% 8.96/9.13  thf('126', plain,
% 8.96/9.13      (![X44 : $i, X45 : $i, X46 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 8.96/9.13          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 8.96/9.13      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.96/9.13  thf('127', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['125', '126'])).
% 8.96/9.13  thf('128', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['35', '38'])).
% 8.96/9.13  thf('129', plain,
% 8.96/9.13      (![X38 : $i, X39 : $i]:
% 8.96/9.13         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 8.96/9.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 8.96/9.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.96/9.13  thf('130', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['128', '129'])).
% 8.96/9.13  thf('131', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 8.96/9.13      inference('sup+', [status(thm)], ['96', '123'])).
% 8.96/9.13  thf('132', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['125', '126'])).
% 8.96/9.13  thf('133', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['128', '129'])).
% 8.96/9.13  thf('134', plain,
% 8.96/9.13      (((~ (v3_pre_topc @ sk_D @ sk_A)
% 8.96/9.13         | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 8.96/9.13             = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)],
% 8.96/9.13                ['46', '124', '127', '130', '131', '132', '133'])).
% 8.96/9.13  thf('135', plain,
% 8.96/9.13      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 8.96/9.13          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['32', '134'])).
% 8.96/9.13  thf('136', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['35', '38'])).
% 8.96/9.13  thf('137', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf(d1_tops_1, axiom,
% 8.96/9.13    (![A:$i]:
% 8.96/9.13     ( ( l1_pre_topc @ A ) =>
% 8.96/9.13       ( ![B:$i]:
% 8.96/9.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13           ( ( k1_tops_1 @ A @ B ) =
% 8.96/9.13             ( k3_subset_1 @
% 8.96/9.13               ( u1_struct_0 @ A ) @ 
% 8.96/9.13               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 8.96/9.13  thf('138', plain,
% 8.96/9.13      (![X58 : $i, X59 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 8.96/9.13          | ((k1_tops_1 @ X59 @ X58)
% 8.96/9.13              = (k3_subset_1 @ (u1_struct_0 @ X59) @ 
% 8.96/9.13                 (k2_pre_topc @ X59 @ (k3_subset_1 @ (u1_struct_0 @ X59) @ X58))))
% 8.96/9.13          | ~ (l1_pre_topc @ X59))),
% 8.96/9.13      inference('cnf', [status(esa)], [d1_tops_1])).
% 8.96/9.13  thf('139', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 8.96/9.13          | ~ (l1_struct_0 @ X0)
% 8.96/9.13          | ~ (l1_pre_topc @ X0)
% 8.96/9.13          | ((k1_tops_1 @ X0 @ X1)
% 8.96/9.13              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 8.96/9.13                 (k2_pre_topc @ X0 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['137', '138'])).
% 8.96/9.13  thf('140', plain,
% 8.96/9.13      (((((k1_tops_1 @ sk_A @ sk_D)
% 8.96/9.13           = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13              (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))
% 8.96/9.13         | ~ (l1_pre_topc @ sk_A)
% 8.96/9.13         | ~ (l1_struct_0 @ sk_A)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['136', '139'])).
% 8.96/9.13  thf('141', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf('142', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('split', [status(esa)], ['4'])).
% 8.96/9.13  thf('143', plain,
% 8.96/9.13      (![X38 : $i, X39 : $i]:
% 8.96/9.13         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 8.96/9.13          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 8.96/9.13      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.96/9.13  thf('144', plain,
% 8.96/9.13      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['142', '143'])).
% 8.96/9.13  thf('145', plain,
% 8.96/9.13      (((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13           = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D))
% 8.96/9.13         | ~ (l1_struct_0 @ sk_A)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['141', '144'])).
% 8.96/9.13  thf('146', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('147', plain,
% 8.96/9.13      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['145', '146'])).
% 8.96/9.13  thf('148', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['128', '129'])).
% 8.96/9.13  thf('149', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['147', '148'])).
% 8.96/9.13  thf('150', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('151', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('152', plain,
% 8.96/9.13      ((((k1_tops_1 @ sk_A @ sk_D)
% 8.96/9.13          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['140', '149', '150', '151'])).
% 8.96/9.13  thf('153', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 8.96/9.13      inference('sup+', [status(thm)], ['96', '123'])).
% 8.96/9.13  thf('154', plain,
% 8.96/9.13      ((((k1_tops_1 @ sk_A @ sk_D)
% 8.96/9.13          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['152', '153'])).
% 8.96/9.13  thf('155', plain,
% 8.96/9.13      ((((k1_tops_1 @ sk_A @ sk_D)
% 8.96/9.13          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))))
% 8.96/9.13         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['135', '154'])).
% 8.96/9.13  thf('156', plain,
% 8.96/9.13      (![X54 : $i]:
% 8.96/9.13         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.96/9.13  thf('157', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.96/9.13      inference('clc', [status(thm)], ['83', '84'])).
% 8.96/9.13  thf('158', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('split', [status(esa)], ['4'])).
% 8.96/9.13  thf('159', plain,
% 8.96/9.13      (![X47 : $i, X48 : $i, X49 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 8.96/9.13          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 8.96/9.13              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 8.96/9.13          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 8.96/9.13      inference('cnf', [status(esa)], [t33_subset_1])).
% 8.96/9.13  thf('160', plain,
% 8.96/9.13      ((![X0 : $i]:
% 8.96/9.13          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13           | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D))
% 8.96/9.13               = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_D))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['158', '159'])).
% 8.96/9.13  thf('161', plain,
% 8.96/9.13      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D))
% 8.96/9.13          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['157', '160'])).
% 8.96/9.13  thf('162', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 8.96/9.13      inference('sup-', [status(thm)], ['125', '126'])).
% 8.96/9.13  thf('163', plain,
% 8.96/9.13      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['142', '143'])).
% 8.96/9.13  thf('164', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['147', '148'])).
% 8.96/9.13  thf('165', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 8.96/9.13          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['163', '164'])).
% 8.96/9.13  thf('166', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.96/9.13      inference('sup+', [status(thm)], ['88', '89'])).
% 8.96/9.13  thf('167', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('split', [status(esa)], ['4'])).
% 8.96/9.13  thf('168', plain,
% 8.96/9.13      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 8.96/9.13      inference('cnf', [status(esa)], [t4_subset_1])).
% 8.96/9.13  thf(redefinition_k4_subset_1, axiom,
% 8.96/9.13    (![A:$i,B:$i,C:$i]:
% 8.96/9.13     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.96/9.13         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.96/9.13       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.96/9.13  thf('169', plain,
% 8.96/9.13      (![X41 : $i, X42 : $i, X43 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 8.96/9.13          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42))
% 8.96/9.13          | ((k4_subset_1 @ X42 @ X41 @ X43) = (k2_xboole_0 @ X41 @ X43)))),
% 8.96/9.13      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.96/9.13  thf('170', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 8.96/9.13            = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 8.96/9.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['168', '169'])).
% 8.96/9.13  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 8.96/9.13  thf('171', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 8.96/9.13      inference('cnf', [status(esa)], [t65_xboole_1])).
% 8.96/9.13  thf(t1_boole, axiom,
% 8.96/9.13    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.96/9.13  thf('172', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 8.96/9.13      inference('cnf', [status(esa)], [t1_boole])).
% 8.96/9.13  thf(t72_xboole_1, axiom,
% 8.96/9.13    (![A:$i,B:$i,C:$i,D:$i]:
% 8.96/9.13     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 8.96/9.13         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 8.96/9.13       ( ( C ) = ( B ) ) ))).
% 8.96/9.13  thf('173', plain,
% 8.96/9.13      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 8.96/9.13         (((X16) = (X15))
% 8.96/9.13          | ~ (r1_xboole_0 @ X16 @ X17)
% 8.96/9.13          | ((k2_xboole_0 @ X17 @ X15) != (k2_xboole_0 @ X16 @ X18))
% 8.96/9.13          | ~ (r1_xboole_0 @ X18 @ X15))),
% 8.96/9.13      inference('cnf', [status(esa)], [t72_xboole_1])).
% 8.96/9.13  thf('174', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.96/9.13         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 8.96/9.13          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 8.96/9.13          | ~ (r1_xboole_0 @ X0 @ X2)
% 8.96/9.13          | ((X0) = (X1)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['172', '173'])).
% 8.96/9.13  thf('175', plain,
% 8.96/9.13      (![X1 : $i, X2 : $i]:
% 8.96/9.13         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 8.96/9.13          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2)
% 8.96/9.13          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 8.96/9.13      inference('simplify', [status(thm)], ['174'])).
% 8.96/9.13  thf('176', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 8.96/9.13      inference('cnf', [status(esa)], [t3_boole])).
% 8.96/9.13  thf('177', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.96/9.13      inference('simplify', [status(thm)], ['66'])).
% 8.96/9.13  thf(t85_xboole_1, axiom,
% 8.96/9.13    (![A:$i,B:$i,C:$i]:
% 8.96/9.13     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 8.96/9.13  thf('178', plain,
% 8.96/9.13      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.96/9.13         (~ (r1_tarski @ X19 @ X20)
% 8.96/9.13          | (r1_xboole_0 @ X19 @ (k4_xboole_0 @ X21 @ X20)))),
% 8.96/9.13      inference('cnf', [status(esa)], [t85_xboole_1])).
% 8.96/9.13  thf('179', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['177', '178'])).
% 8.96/9.13  thf('180', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 8.96/9.13      inference('sup+', [status(thm)], ['176', '179'])).
% 8.96/9.13  thf('181', plain,
% 8.96/9.13      (![X1 : $i, X2 : $i]:
% 8.96/9.13         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 8.96/9.13          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2))),
% 8.96/9.13      inference('demod', [status(thm)], ['175', '180'])).
% 8.96/9.13  thf('182', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.96/9.13      inference('sup-', [status(thm)], ['171', '181'])).
% 8.96/9.13  thf('183', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i]:
% 8.96/9.13         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1) = (X1))
% 8.96/9.13          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 8.96/9.13      inference('demod', [status(thm)], ['170', '182'])).
% 8.96/9.13  thf('184', plain,
% 8.96/9.13      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_D) = (sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['167', '183'])).
% 8.96/9.13  thf('185', plain,
% 8.96/9.13      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.96/9.13          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['161', '162', '165', '166', '184'])).
% 8.96/9.13  thf('186', plain,
% 8.96/9.13      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13           (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D))
% 8.96/9.13         | ~ (l1_struct_0 @ sk_A)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['156', '185'])).
% 8.96/9.13  thf('187', plain, ((l1_struct_0 @ sk_A)),
% 8.96/9.13      inference('sup-', [status(thm)], ['36', '37'])).
% 8.96/9.13  thf('188', plain,
% 8.96/9.13      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 8.96/9.13          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['186', '187'])).
% 8.96/9.13  thf('189', plain,
% 8.96/9.13      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 8.96/9.13         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup+', [status(thm)], ['155', '188'])).
% 8.96/9.13  thf('190', plain,
% 8.96/9.13      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 8.96/9.13      inference('split', [status(esa)], ['2'])).
% 8.96/9.13  thf('191', plain,
% 8.96/9.13      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('192', plain,
% 8.96/9.13      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('split', [status(esa)], ['4'])).
% 8.96/9.13  thf(t48_tops_1, axiom,
% 8.96/9.13    (![A:$i]:
% 8.96/9.13     ( ( l1_pre_topc @ A ) =>
% 8.96/9.13       ( ![B:$i]:
% 8.96/9.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13           ( ![C:$i]:
% 8.96/9.13             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.96/9.13               ( ( r1_tarski @ B @ C ) =>
% 8.96/9.13                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.96/9.13  thf('193', plain,
% 8.96/9.13      (![X66 : $i, X67 : $i, X68 : $i]:
% 8.96/9.13         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 8.96/9.13          | ~ (r1_tarski @ X66 @ X68)
% 8.96/9.13          | (r1_tarski @ (k1_tops_1 @ X67 @ X66) @ (k1_tops_1 @ X67 @ X68))
% 8.96/9.13          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 8.96/9.13          | ~ (l1_pre_topc @ X67))),
% 8.96/9.13      inference('cnf', [status(esa)], [t48_tops_1])).
% 8.96/9.13  thf('194', plain,
% 8.96/9.13      ((![X0 : $i]:
% 8.96/9.13          (~ (l1_pre_topc @ sk_A)
% 8.96/9.13           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 8.96/9.13           | ~ (r1_tarski @ sk_D @ X0)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['192', '193'])).
% 8.96/9.13  thf('195', plain, ((l1_pre_topc @ sk_A)),
% 8.96/9.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.96/9.13  thf('196', plain,
% 8.96/9.13      ((![X0 : $i]:
% 8.96/9.13          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.96/9.13           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 8.96/9.13           | ~ (r1_tarski @ sk_D @ X0)))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('demod', [status(thm)], ['194', '195'])).
% 8.96/9.13  thf('197', plain,
% 8.96/9.13      (((~ (r1_tarski @ sk_D @ sk_C_1)
% 8.96/9.13         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 8.96/9.13         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['191', '196'])).
% 8.96/9.13  thf('198', plain,
% 8.96/9.13      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 8.96/9.13         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['190', '197'])).
% 8.96/9.13  thf('199', plain,
% 8.96/9.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.96/9.13         (~ (r2_hidden @ X0 @ X1)
% 8.96/9.13          | (r2_hidden @ X0 @ X2)
% 8.96/9.13          | ~ (r1_tarski @ X1 @ X2))),
% 8.96/9.13      inference('cnf', [status(esa)], [d3_tarski])).
% 8.96/9.13  thf('200', plain,
% 8.96/9.13      ((![X0 : $i]:
% 8.96/9.13          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 8.96/9.13           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))))
% 8.96/9.13         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['198', '199'])).
% 8.96/9.13  thf('201', plain,
% 8.96/9.13      ((![X0 : $i]:
% 8.96/9.13          (~ (r2_hidden @ X0 @ sk_D)
% 8.96/9.13           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 8.96/9.13         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 8.96/9.13             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['189', '200'])).
% 8.96/9.13  thf('202', plain,
% 8.96/9.13      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 8.96/9.13         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 8.96/9.13             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 8.96/9.13             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 8.96/9.13             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 8.96/9.13      inference('sup-', [status(thm)], ['31', '201'])).
% 8.96/9.13  thf('203', plain,
% 8.96/9.13      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 8.96/9.13         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 8.96/9.13      inference('split', [status(esa)], ['6'])).
% 8.96/9.13  thf('204', plain,
% 8.96/9.13      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 8.96/9.13       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 8.96/9.13       ~ ((r1_tarski @ sk_D @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 8.96/9.13       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 8.96/9.13      inference('sup-', [status(thm)], ['202', '203'])).
% 8.96/9.13  thf('205', plain, ($false),
% 8.96/9.13      inference('sat_resolution*', [status(thm)],
% 8.96/9.13                ['1', '3', '5', '7', '28', '30', '204'])).
% 8.96/9.13  
% 8.96/9.13  % SZS output end Refutation
% 8.96/9.13  
% 8.96/9.14  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
