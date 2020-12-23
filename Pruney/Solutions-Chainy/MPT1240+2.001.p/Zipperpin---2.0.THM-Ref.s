%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sBDUzJsJQ7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:05 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  255 (1236 expanded)
%              Number of leaves         :   55 ( 411 expanded)
%              Depth                    :   19
%              Number of atoms          : 2404 (12853 expanded)
%              Number of equality atoms :  128 ( 639 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('33',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

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

thf('34',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X57 ) ) )
      | ~ ( v3_pre_topc @ X56 @ X57 )
      | ( ( k2_pre_topc @ X57 @ ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_struct_0 @ X57 ) @ X56 ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ X57 ) @ ( k2_struct_0 @ X57 ) @ X56 ) )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[t53_pre_topc])).

thf('35',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('39',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('41',plain,
    ( ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('43',plain,(
    ! [X55: $i] :
      ( ( l1_struct_0 @ X55 )
      | ~ ( l1_pre_topc @ X55 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('46',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('47',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_D ) )
          = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_D ) )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('50',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = ( k4_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('52',plain,(
    ! [X20: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('55',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('57',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('60',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('64',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D ) )
          = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_D ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('70',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['61','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('73',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['60','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('76',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','53','58','59','76'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('78',plain,(
    ! [X34: $i] :
      ( r1_tarski @ ( k1_tarski @ X34 ) @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(t56_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('79',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t56_zfmisc_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('80',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('82',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ X23 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','83'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('85',plain,(
    ! [X29: $i,X30: $i] :
      ( ( X30 != X29 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X30 ) @ ( k1_tarski @ X29 ) )
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('86',plain,(
    ! [X29: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X29 ) @ ( k1_tarski @ X29 ) )
     != ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('88',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('90',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X29: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X29 ) ) ),
    inference(demod,[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['84','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','93'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('95',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ( m1_subset_1 @ X35 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('97',plain,(
    ! [X40: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('98',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) )
      | ( ( k7_subset_1 @ X45 @ X44 @ X46 )
        = ( k4_xboole_0 @ X44 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('102',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','53','58','59','76'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('106',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('107',plain,
    ( ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
        = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      | ~ ( v3_pre_topc @ sk_D @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['37','77','100','103','104','105','106'])).

thf('108',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['32','107'])).

thf('109',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X58: $i,X59: $i] :
      ( ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X59 ) ) )
      | ( ( k1_tops_1 @ X59 @ X58 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ ( k2_pre_topc @ X59 @ ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ X58 ) ) ) )
      | ~ ( l1_pre_topc @ X59 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('111',plain,
    ( ( ~ ( l1_pre_topc @ sk_A )
      | ( ( k1_tops_1 @ sk_A @ sk_D )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','53','58','59','76'])).

thf('115',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['48','53','58','59','76'])).

thf('116',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) ) )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['108','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_D ) )
          = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_D ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('120',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('122',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k3_subset_1 @ X38 @ X39 )
        = ( k4_xboole_0 @ X38 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('127',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('128',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X42 ) )
      | ( ( k4_subset_1 @ X42 @ X41 @ X43 )
        = ( k2_xboole_0 @ X41 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['80'])).

thf(t117_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ C @ B )
     => ( ( k4_xboole_0 @ A @ C )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ) )).

thf('131',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = ( k2_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ ( k3_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) )
      | ~ ( r1_tarski @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t117_xboole_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('134',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['132','133','134','135'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('137',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X17: $i] :
      ( ( k4_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X1 )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['129','140'])).

thf('142',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_D )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['126','141'])).

thf('143',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['120','125','142'])).

thf('144',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('145',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('146',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('149',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) )
        = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_C_1 ) )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('156',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['152','153','154','155'])).

thf('157',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('158',plain,(
    ! [X54: $i] :
      ( ( ( k2_struct_0 @ X54 )
        = ( u1_struct_0 @ X54 ) )
      | ~ ( l1_struct_0 @ X54 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('159',plain,(
    ! [X50: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('160',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( ( k3_subset_1 @ X48 @ ( k7_subset_1 @ X48 @ X49 @ X47 ) )
        = ( k4_subset_1 @ X48 @ ( k3_subset_1 @ X48 @ X49 ) @ X47 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ sk_C_1 ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['159','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('167',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['158','167'])).

thf('169',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('170',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['157','170'])).

thf('172',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('173',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k4_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','173'])).

thf('175',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','173'])).

thf('176',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','173'])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('178',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('179',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_D ) )
      = sk_D )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['143','174','175','176','177','178'])).

thf('180',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_D )
      = sk_D )
   <= ( ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup+',[status(thm)],['117','179'])).

thf('181',plain,
    ( ( r1_tarski @ sk_D @ sk_C_1 )
   <= ( r1_tarski @ sk_D @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('182',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('183',plain,
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

thf('184',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ~ ( m1_subset_1 @ X66 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( r1_tarski @ X66 @ X68 )
      | ( r1_tarski @ ( k1_tops_1 @ X67 @ X66 ) @ ( k1_tops_1 @ X67 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X67 ) ) )
      | ~ ( l1_pre_topc @ X67 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('185',plain,
    ( ! [X0: $i] :
        ( ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['156','173'])).

thf('189',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
        | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ X0 ) )
        | ~ ( r1_tarski @ sk_D @ X0 ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,
    ( ( ~ ( r1_tarski @ sk_D @ sk_C_1 )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['182','189'])).

thf('191',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_D ) @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['181','190'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('192',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('193',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_D ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_D )
        | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) )
   <= ( ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['180','193'])).

thf('195',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ( ( r2_hidden @ sk_B @ sk_D )
      & ( r1_tarski @ sk_D @ sk_C_1 )
      & ( v3_pre_topc @ sk_D @ sk_A )
      & ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['31','194'])).

thf('196',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('197',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ sk_D @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_D )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','28','30','197'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sBDUzJsJQ7
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.67/2.85  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.67/2.85  % Solved by: fo/fo7.sh
% 2.67/2.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.67/2.85  % done 7360 iterations in 2.395s
% 2.67/2.85  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.67/2.85  % SZS output start Refutation
% 2.67/2.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.67/2.85  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.67/2.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.67/2.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.67/2.85  thf(sk_B_type, type, sk_B: $i).
% 2.67/2.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.67/2.85  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.67/2.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.67/2.85  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.67/2.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.67/2.85  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 2.67/2.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.67/2.85  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 2.67/2.85  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.67/2.85  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.67/2.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.67/2.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.67/2.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.67/2.85  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.67/2.85  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.67/2.85  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.67/2.85  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.67/2.85  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.67/2.85  thf(sk_A_type, type, sk_A: $i).
% 2.67/2.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.67/2.85  thf(sk_D_type, type, sk_D: $i).
% 2.67/2.85  thf(t54_tops_1, conjecture,
% 2.67/2.85    (![A:$i]:
% 2.67/2.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.85       ( ![B:$i,C:$i]:
% 2.67/2.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85           ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 2.67/2.85             ( ?[D:$i]:
% 2.67/2.85               ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 2.67/2.85                 ( v3_pre_topc @ D @ A ) & 
% 2.67/2.85                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 2.67/2.85  thf(zf_stmt_0, negated_conjecture,
% 2.67/2.85    (~( ![A:$i]:
% 2.67/2.85        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 2.67/2.85          ( ![B:$i,C:$i]:
% 2.67/2.85            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85              ( ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) <=>
% 2.67/2.85                ( ?[D:$i]:
% 2.67/2.85                  ( ( r2_hidden @ B @ D ) & ( r1_tarski @ D @ C ) & 
% 2.67/2.85                    ( v3_pre_topc @ D @ A ) & 
% 2.67/2.85                    ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 2.67/2.85    inference('cnf.neg', [status(esa)], [t54_tops_1])).
% 2.67/2.85  thf('0', plain,
% 2.67/2.85      (((r2_hidden @ sk_B @ sk_D)
% 2.67/2.85        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('1', plain,
% 2.67/2.85      (((r2_hidden @ sk_B @ sk_D)) | 
% 2.67/2.85       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('split', [status(esa)], ['0'])).
% 2.67/2.85  thf('2', plain,
% 2.67/2.85      (((r1_tarski @ sk_D @ sk_C_1)
% 2.67/2.85        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('3', plain,
% 2.67/2.85      (((r1_tarski @ sk_D @ sk_C_1)) | 
% 2.67/2.85       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('split', [status(esa)], ['2'])).
% 2.67/2.85  thf('4', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('5', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 2.67/2.85       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf('6', plain,
% 2.67/2.85      (![X69 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85          | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85          | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85          | ~ (r2_hidden @ sk_B @ X69)
% 2.67/2.85          | ~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('7', plain,
% 2.67/2.85      ((![X69 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85           | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85           | ~ (r2_hidden @ sk_B @ X69))) | 
% 2.67/2.85       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('split', [status(esa)], ['6'])).
% 2.67/2.85  thf('8', plain,
% 2.67/2.85      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 2.67/2.85         <= (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 2.67/2.85      inference('split', [status(esa)], ['0'])).
% 2.67/2.85  thf('9', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf(dt_k1_tops_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( ( l1_pre_topc @ A ) & 
% 2.67/2.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.67/2.85       ( m1_subset_1 @
% 2.67/2.85         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.67/2.85  thf('10', plain,
% 2.67/2.85      (![X60 : $i, X61 : $i]:
% 2.67/2.85         (~ (l1_pre_topc @ X60)
% 2.67/2.85          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 2.67/2.85          | (m1_subset_1 @ (k1_tops_1 @ X60 @ X61) @ 
% 2.67/2.85             (k1_zfmisc_1 @ (u1_struct_0 @ X60))))),
% 2.67/2.85      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 2.67/2.85  thf('11', plain,
% 2.67/2.85      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.85         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85        | ~ (l1_pre_topc @ sk_A))),
% 2.67/2.85      inference('sup-', [status(thm)], ['9', '10'])).
% 2.67/2.85  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('13', plain,
% 2.67/2.85      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_C_1) @ 
% 2.67/2.85        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.85      inference('demod', [status(thm)], ['11', '12'])).
% 2.67/2.85  thf('14', plain,
% 2.67/2.85      ((![X69 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85           | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85           | ~ (r2_hidden @ sk_B @ X69)))
% 2.67/2.85         <= ((![X69 : $i]:
% 2.67/2.85                (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85                 | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85                 | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85                 | ~ (r2_hidden @ sk_B @ X69))))),
% 2.67/2.85      inference('split', [status(esa)], ['6'])).
% 2.67/2.85  thf('15', plain,
% 2.67/2.85      (((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))
% 2.67/2.85         | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 2.67/2.85         | ~ (v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)))
% 2.67/2.85         <= ((![X69 : $i]:
% 2.67/2.85                (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85                 | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85                 | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85                 | ~ (r2_hidden @ sk_B @ X69))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['13', '14'])).
% 2.67/2.85  thf('16', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf(t44_tops_1, axiom,
% 2.67/2.85    (![A:$i]:
% 2.67/2.85     ( ( l1_pre_topc @ A ) =>
% 2.67/2.85       ( ![B:$i]:
% 2.67/2.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.67/2.85  thf('17', plain,
% 2.67/2.85      (![X64 : $i, X65 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (u1_struct_0 @ X65)))
% 2.67/2.85          | (r1_tarski @ (k1_tops_1 @ X65 @ X64) @ X64)
% 2.67/2.85          | ~ (l1_pre_topc @ X65))),
% 2.67/2.85      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.67/2.85  thf('18', plain,
% 2.67/2.85      ((~ (l1_pre_topc @ sk_A)
% 2.67/2.85        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['16', '17'])).
% 2.67/2.85  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('20', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 2.67/2.85      inference('demod', [status(thm)], ['18', '19'])).
% 2.67/2.85  thf('21', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf(fc9_tops_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 2.67/2.85         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.67/2.85       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 2.67/2.85  thf('22', plain,
% 2.67/2.85      (![X62 : $i, X63 : $i]:
% 2.67/2.85         (~ (l1_pre_topc @ X62)
% 2.67/2.85          | ~ (v2_pre_topc @ X62)
% 2.67/2.85          | ~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 2.67/2.85          | (v3_pre_topc @ (k1_tops_1 @ X62 @ X63) @ X62))),
% 2.67/2.85      inference('cnf', [status(esa)], [fc9_tops_1])).
% 2.67/2.85  thf('23', plain,
% 2.67/2.85      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)
% 2.67/2.85        | ~ (v2_pre_topc @ sk_A)
% 2.67/2.85        | ~ (l1_pre_topc @ sk_A))),
% 2.67/2.85      inference('sup-', [status(thm)], ['21', '22'])).
% 2.67/2.85  thf('24', plain, ((v2_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('26', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C_1) @ sk_A)),
% 2.67/2.85      inference('demod', [status(thm)], ['23', '24', '25'])).
% 2.67/2.85  thf('27', plain,
% 2.67/2.85      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 2.67/2.85         <= ((![X69 : $i]:
% 2.67/2.85                (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85                 | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85                 | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85                 | ~ (r2_hidden @ sk_B @ X69))))),
% 2.67/2.85      inference('demod', [status(thm)], ['15', '20', '26'])).
% 2.67/2.85  thf('28', plain,
% 2.67/2.85      (~
% 2.67/2.85       (![X69 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X69 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | ~ (v3_pre_topc @ X69 @ sk_A)
% 2.67/2.85           | ~ (r1_tarski @ X69 @ sk_C_1)
% 2.67/2.85           | ~ (r2_hidden @ sk_B @ X69))) | 
% 2.67/2.85       ~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['8', '27'])).
% 2.67/2.85  thf('29', plain,
% 2.67/2.85      (((v3_pre_topc @ sk_D @ sk_A)
% 2.67/2.85        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('30', plain,
% 2.67/2.85      (((v3_pre_topc @ sk_D @ sk_A)) | 
% 2.67/2.85       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('split', [status(esa)], ['29'])).
% 2.67/2.85  thf('31', plain,
% 2.67/2.85      (((r2_hidden @ sk_B @ sk_D)) <= (((r2_hidden @ sk_B @ sk_D)))),
% 2.67/2.85      inference('split', [status(esa)], ['0'])).
% 2.67/2.85  thf('32', plain,
% 2.67/2.85      (((v3_pre_topc @ sk_D @ sk_A)) <= (((v3_pre_topc @ sk_D @ sk_A)))),
% 2.67/2.85      inference('split', [status(esa)], ['29'])).
% 2.67/2.85  thf('33', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf(t53_pre_topc, axiom,
% 2.67/2.85    (![A:$i]:
% 2.67/2.85     ( ( l1_pre_topc @ A ) =>
% 2.67/2.85       ( ![B:$i]:
% 2.67/2.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85           ( ( ( v3_pre_topc @ B @ A ) =>
% 2.67/2.85               ( ( k2_pre_topc @
% 2.67/2.85                   A @ 
% 2.67/2.85                   ( k7_subset_1 @
% 2.67/2.85                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 2.67/2.85                 ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) & 
% 2.67/2.85             ( ( ( v2_pre_topc @ A ) & 
% 2.67/2.85                 ( ( k2_pre_topc @
% 2.67/2.85                     A @ 
% 2.67/2.85                     ( k7_subset_1 @
% 2.67/2.85                       ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) =
% 2.67/2.85                   ( k7_subset_1 @
% 2.67/2.85                     ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) ) ) =>
% 2.67/2.85               ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 2.67/2.85  thf('34', plain,
% 2.67/2.85      (![X56 : $i, X57 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (u1_struct_0 @ X57)))
% 2.67/2.85          | ~ (v3_pre_topc @ X56 @ X57)
% 2.67/2.85          | ((k2_pre_topc @ X57 @ 
% 2.67/2.85              (k7_subset_1 @ (u1_struct_0 @ X57) @ (k2_struct_0 @ X57) @ X56))
% 2.67/2.85              = (k7_subset_1 @ (u1_struct_0 @ X57) @ (k2_struct_0 @ X57) @ X56))
% 2.67/2.85          | ~ (l1_pre_topc @ X57))),
% 2.67/2.85      inference('cnf', [status(esa)], [t53_pre_topc])).
% 2.67/2.85  thf('35', plain,
% 2.67/2.85      (((~ (l1_pre_topc @ sk_A)
% 2.67/2.85         | ((k2_pre_topc @ sk_A @ 
% 2.67/2.85             (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85             = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85                sk_D))
% 2.67/2.85         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['33', '34'])).
% 2.67/2.85  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('37', plain,
% 2.67/2.85      (((((k2_pre_topc @ sk_A @ 
% 2.67/2.85           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85           = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['35', '36'])).
% 2.67/2.85  thf(t4_subset_1, axiom,
% 2.67/2.85    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 2.67/2.85  thf('38', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf(d3_struct_0, axiom,
% 2.67/2.85    (![A:$i]:
% 2.67/2.85     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.67/2.85  thf('39', plain,
% 2.67/2.85      (![X54 : $i]:
% 2.67/2.85         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.67/2.85  thf('40', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf('41', plain,
% 2.67/2.85      ((((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.67/2.85         | ~ (l1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup+', [status(thm)], ['39', '40'])).
% 2.67/2.85  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf(dt_l1_pre_topc, axiom,
% 2.67/2.85    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 2.67/2.85  thf('43', plain,
% 2.67/2.85      (![X55 : $i]: ((l1_struct_0 @ X55) | ~ (l1_pre_topc @ X55))),
% 2.67/2.85      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 2.67/2.85  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 2.67/2.85      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.85  thf('45', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['41', '44'])).
% 2.67/2.85  thf(t33_subset_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.85       ( ![C:$i]:
% 2.67/2.85         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.85           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.67/2.85             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.67/2.85  thf('46', plain,
% 2.67/2.85      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 2.67/2.85          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 2.67/2.85              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 2.67/2.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 2.67/2.85      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.67/2.85  thf('47', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.67/2.85           | ((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85               (k7_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_D))
% 2.67/2.85               = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85                  (k3_subset_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_D))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['45', '46'])).
% 2.67/2.85  thf('48', plain,
% 2.67/2.85      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85          (k7_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0 @ sk_D))
% 2.67/2.85          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['38', '47'])).
% 2.67/2.85  thf('49', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf(redefinition_k7_subset_1, axiom,
% 2.67/2.85    (![A:$i,B:$i,C:$i]:
% 2.67/2.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.85       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 2.67/2.85  thf('50', plain,
% 2.67/2.85      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 2.67/2.85          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 2.67/2.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.67/2.85  thf('51', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 2.67/2.85           = (k4_xboole_0 @ k1_xboole_0 @ X1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['49', '50'])).
% 2.67/2.85  thf(t4_boole, axiom,
% 2.67/2.85    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 2.67/2.85  thf('52', plain,
% 2.67/2.85      (![X20 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X20) = (k1_xboole_0))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_boole])).
% 2.67/2.85  thf('53', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['51', '52'])).
% 2.67/2.85  thf('54', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf(d5_subset_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.67/2.85       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.67/2.85  thf('55', plain,
% 2.67/2.85      (![X38 : $i, X39 : $i]:
% 2.67/2.85         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 2.67/2.85          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 2.67/2.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.67/2.85  thf('56', plain,
% 2.67/2.85      (![X0 : $i]:
% 2.67/2.85         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 2.67/2.85      inference('sup-', [status(thm)], ['54', '55'])).
% 2.67/2.85  thf(t3_boole, axiom,
% 2.67/2.85    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.67/2.85  thf('57', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.67/2.85      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.85  thf('58', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('59', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('60', plain,
% 2.67/2.85      (![X54 : $i]:
% 2.67/2.85         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.67/2.85  thf('61', plain,
% 2.67/2.85      (![X54 : $i]:
% 2.67/2.85         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.67/2.85  thf('62', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf('63', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf('64', plain,
% 2.67/2.85      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 2.67/2.85          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 2.67/2.85              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 2.67/2.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 2.67/2.85      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.67/2.85  thf('65', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D))
% 2.67/2.85               = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_D))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['63', '64'])).
% 2.67/2.85  thf('66', plain,
% 2.67/2.85      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_D))
% 2.67/2.85          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['62', '65'])).
% 2.67/2.85  thf('67', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['51', '52'])).
% 2.67/2.85  thf('68', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('69', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('70', plain,
% 2.67/2.85      ((((u1_struct_0 @ sk_A)
% 2.67/2.85          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 2.67/2.85  thf('71', plain,
% 2.67/2.85      (((((u1_struct_0 @ sk_A)
% 2.67/2.85           = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85         | ~ (l1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup+', [status(thm)], ['61', '70'])).
% 2.67/2.85  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 2.67/2.85      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.85  thf('73', plain,
% 2.67/2.85      ((((u1_struct_0 @ sk_A)
% 2.67/2.85          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['71', '72'])).
% 2.67/2.85  thf('74', plain,
% 2.67/2.85      (((((u1_struct_0 @ sk_A)
% 2.67/2.85           = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85         | ~ (l1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup+', [status(thm)], ['60', '73'])).
% 2.67/2.85  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 2.67/2.85      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.85  thf('76', plain,
% 2.67/2.85      ((((u1_struct_0 @ sk_A)
% 2.67/2.85          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['74', '75'])).
% 2.67/2.85  thf('77', plain,
% 2.67/2.85      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['48', '53', '58', '59', '76'])).
% 2.67/2.85  thf(t80_zfmisc_1, axiom,
% 2.67/2.85    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.67/2.85  thf('78', plain,
% 2.67/2.85      (![X34 : $i]: (r1_tarski @ (k1_tarski @ X34) @ (k1_zfmisc_1 @ X34))),
% 2.67/2.85      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 2.67/2.85  thf(t56_zfmisc_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.67/2.85  thf('79', plain,
% 2.67/2.85      (![X32 : $i, X33 : $i]:
% 2.67/2.85         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 2.67/2.85      inference('cnf', [status(esa)], [t56_zfmisc_1])).
% 2.67/2.85  thf(d10_xboole_0, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.67/2.85  thf('80', plain,
% 2.67/2.85      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 2.67/2.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.67/2.85  thf('81', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.67/2.85      inference('simplify', [status(thm)], ['80'])).
% 2.67/2.85  thf(t67_xboole_1, axiom,
% 2.67/2.85    (![A:$i,B:$i,C:$i]:
% 2.67/2.85     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 2.67/2.85         ( r1_xboole_0 @ B @ C ) ) =>
% 2.67/2.85       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.67/2.85  thf('82', plain,
% 2.67/2.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.67/2.85         (((X21) = (k1_xboole_0))
% 2.67/2.85          | ~ (r1_tarski @ X21 @ X22)
% 2.67/2.85          | ~ (r1_tarski @ X21 @ X23)
% 2.67/2.85          | ~ (r1_xboole_0 @ X22 @ X23))),
% 2.67/2.85      inference('cnf', [status(esa)], [t67_xboole_1])).
% 2.67/2.85  thf('83', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         (~ (r1_xboole_0 @ X0 @ X1)
% 2.67/2.85          | ~ (r1_tarski @ X0 @ X1)
% 2.67/2.85          | ((X0) = (k1_xboole_0)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['81', '82'])).
% 2.67/2.85  thf('84', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((r2_hidden @ X1 @ X0)
% 2.67/2.85          | ((k1_tarski @ X1) = (k1_xboole_0))
% 2.67/2.85          | ~ (r1_tarski @ (k1_tarski @ X1) @ X0))),
% 2.67/2.85      inference('sup-', [status(thm)], ['79', '83'])).
% 2.67/2.85  thf(t20_zfmisc_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 2.67/2.85         ( k1_tarski @ A ) ) <=>
% 2.67/2.85       ( ( A ) != ( B ) ) ))).
% 2.67/2.85  thf('85', plain,
% 2.67/2.85      (![X29 : $i, X30 : $i]:
% 2.67/2.85         (((X30) != (X29))
% 2.67/2.85          | ((k4_xboole_0 @ (k1_tarski @ X30) @ (k1_tarski @ X29))
% 2.67/2.85              != (k1_tarski @ X30)))),
% 2.67/2.85      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 2.67/2.85  thf('86', plain,
% 2.67/2.85      (![X29 : $i]:
% 2.67/2.85         ((k4_xboole_0 @ (k1_tarski @ X29) @ (k1_tarski @ X29))
% 2.67/2.85           != (k1_tarski @ X29))),
% 2.67/2.85      inference('simplify', [status(thm)], ['85'])).
% 2.67/2.85  thf('87', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.67/2.85      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.85  thf(t48_xboole_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.67/2.85  thf('88', plain,
% 2.67/2.85      (![X18 : $i, X19 : $i]:
% 2.67/2.85         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 2.67/2.85           = (k3_xboole_0 @ X18 @ X19))),
% 2.67/2.85      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.67/2.85  thf('89', plain,
% 2.67/2.85      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['87', '88'])).
% 2.67/2.85  thf(t2_boole, axiom,
% 2.67/2.85    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 2.67/2.85  thf('90', plain,
% 2.67/2.85      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 2.67/2.85      inference('cnf', [status(esa)], [t2_boole])).
% 2.67/2.85  thf('91', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['89', '90'])).
% 2.67/2.85  thf('92', plain, (![X29 : $i]: ((k1_xboole_0) != (k1_tarski @ X29))),
% 2.67/2.85      inference('demod', [status(thm)], ['86', '91'])).
% 2.67/2.85  thf('93', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         (~ (r1_tarski @ (k1_tarski @ X1) @ X0) | (r2_hidden @ X1 @ X0))),
% 2.67/2.85      inference('clc', [status(thm)], ['84', '92'])).
% 2.67/2.85  thf('94', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.67/2.85      inference('sup-', [status(thm)], ['78', '93'])).
% 2.67/2.85  thf(d2_subset_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( ( v1_xboole_0 @ A ) =>
% 2.67/2.85         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 2.67/2.85       ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.67/2.85         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 2.67/2.85  thf('95', plain,
% 2.67/2.85      (![X35 : $i, X36 : $i]:
% 2.67/2.85         (~ (r2_hidden @ X35 @ X36)
% 2.67/2.85          | (m1_subset_1 @ X35 @ X36)
% 2.67/2.85          | (v1_xboole_0 @ X36))),
% 2.67/2.85      inference('cnf', [status(esa)], [d2_subset_1])).
% 2.67/2.85  thf('96', plain,
% 2.67/2.85      (![X0 : $i]:
% 2.67/2.85         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 2.67/2.85          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['94', '95'])).
% 2.67/2.85  thf(fc1_subset_1, axiom,
% 2.67/2.85    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.67/2.85  thf('97', plain, (![X40 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X40))),
% 2.67/2.85      inference('cnf', [status(esa)], [fc1_subset_1])).
% 2.67/2.85  thf('98', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.67/2.85      inference('clc', [status(thm)], ['96', '97'])).
% 2.67/2.85  thf('99', plain,
% 2.67/2.85      (![X44 : $i, X45 : $i, X46 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45))
% 2.67/2.85          | ((k7_subset_1 @ X45 @ X44 @ X46) = (k4_xboole_0 @ X44 @ X46)))),
% 2.67/2.85      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 2.67/2.85  thf('100', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['98', '99'])).
% 2.67/2.85  thf('101', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['41', '44'])).
% 2.67/2.85  thf('102', plain,
% 2.67/2.85      (![X38 : $i, X39 : $i]:
% 2.67/2.85         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 2.67/2.85          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 2.67/2.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.67/2.85  thf('103', plain,
% 2.67/2.85      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 2.67/2.85          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['101', '102'])).
% 2.67/2.85  thf('104', plain,
% 2.67/2.85      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['48', '53', '58', '59', '76'])).
% 2.67/2.85  thf('105', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['98', '99'])).
% 2.67/2.85  thf('106', plain,
% 2.67/2.85      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 2.67/2.85          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['101', '102'])).
% 2.67/2.85  thf('107', plain,
% 2.67/2.85      (((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85           = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85         | ~ (v3_pre_topc @ sk_D @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)],
% 2.67/2.85                ['37', '77', '100', '103', '104', '105', '106'])).
% 2.67/2.85  thf('108', plain,
% 2.67/2.85      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['32', '107'])).
% 2.67/2.85  thf('109', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf(d1_tops_1, axiom,
% 2.67/2.85    (![A:$i]:
% 2.67/2.85     ( ( l1_pre_topc @ A ) =>
% 2.67/2.85       ( ![B:$i]:
% 2.67/2.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85           ( ( k1_tops_1 @ A @ B ) =
% 2.67/2.85             ( k3_subset_1 @
% 2.67/2.85               ( u1_struct_0 @ A ) @ 
% 2.67/2.85               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 2.67/2.85  thf('110', plain,
% 2.67/2.85      (![X58 : $i, X59 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (u1_struct_0 @ X59)))
% 2.67/2.85          | ((k1_tops_1 @ X59 @ X58)
% 2.67/2.85              = (k3_subset_1 @ (u1_struct_0 @ X59) @ 
% 2.67/2.85                 (k2_pre_topc @ X59 @ (k3_subset_1 @ (u1_struct_0 @ X59) @ X58))))
% 2.67/2.85          | ~ (l1_pre_topc @ X59))),
% 2.67/2.85      inference('cnf', [status(esa)], [d1_tops_1])).
% 2.67/2.85  thf('111', plain,
% 2.67/2.85      (((~ (l1_pre_topc @ sk_A)
% 2.67/2.85         | ((k1_tops_1 @ sk_A @ sk_D)
% 2.67/2.85             = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85                (k2_pre_topc @ sk_A @ 
% 2.67/2.85                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D))))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['109', '110'])).
% 2.67/2.85  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('113', plain,
% 2.67/2.85      ((((k1_tops_1 @ sk_A @ sk_D)
% 2.67/2.85          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_D)))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['111', '112'])).
% 2.67/2.85  thf('114', plain,
% 2.67/2.85      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['48', '53', '58', '59', '76'])).
% 2.67/2.85  thf('115', plain,
% 2.67/2.85      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['48', '53', '58', '59', '76'])).
% 2.67/2.85  thf('116', plain,
% 2.67/2.85      ((((k1_tops_1 @ sk_A @ sk_D)
% 2.67/2.85          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['113', '114', '115'])).
% 2.67/2.85  thf('117', plain,
% 2.67/2.85      ((((k1_tops_1 @ sk_A @ sk_D)
% 2.67/2.85          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85             (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D))))
% 2.67/2.85         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup+', [status(thm)], ['108', '116'])).
% 2.67/2.85  thf('118', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.67/2.85      inference('clc', [status(thm)], ['96', '97'])).
% 2.67/2.85  thf('119', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85               (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_D))
% 2.67/2.85               = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_D))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['63', '64'])).
% 2.67/2.85  thf('120', plain,
% 2.67/2.85      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85          = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['118', '119'])).
% 2.67/2.85  thf('121', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.67/2.85      inference('clc', [status(thm)], ['96', '97'])).
% 2.67/2.85  thf('122', plain,
% 2.67/2.85      (![X38 : $i, X39 : $i]:
% 2.67/2.85         (((k3_subset_1 @ X38 @ X39) = (k4_xboole_0 @ X38 @ X39))
% 2.67/2.85          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38)))),
% 2.67/2.85      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.67/2.85  thf('123', plain,
% 2.67/2.85      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.67/2.85      inference('sup-', [status(thm)], ['121', '122'])).
% 2.67/2.85  thf('124', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['89', '90'])).
% 2.67/2.85  thf('125', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['123', '124'])).
% 2.67/2.85  thf('126', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf('127', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf(redefinition_k4_subset_1, axiom,
% 2.67/2.85    (![A:$i,B:$i,C:$i]:
% 2.67/2.85     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 2.67/2.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.67/2.85       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 2.67/2.85  thf('128', plain,
% 2.67/2.85      (![X41 : $i, X42 : $i, X43 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 2.67/2.85          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X42))
% 2.67/2.85          | ((k4_subset_1 @ X42 @ X41 @ X43) = (k2_xboole_0 @ X41 @ X43)))),
% 2.67/2.85      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 2.67/2.85  thf('129', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1)
% 2.67/2.85            = (k2_xboole_0 @ k1_xboole_0 @ X1))
% 2.67/2.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['127', '128'])).
% 2.67/2.85  thf('130', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 2.67/2.85      inference('simplify', [status(thm)], ['80'])).
% 2.67/2.85  thf(t117_xboole_1, axiom,
% 2.67/2.85    (![A:$i,B:$i,C:$i]:
% 2.67/2.85     ( ( r1_tarski @ C @ B ) =>
% 2.67/2.85       ( ( k4_xboole_0 @ A @ C ) =
% 2.67/2.85         ( k2_xboole_0 @
% 2.67/2.85           ( k4_xboole_0 @ A @ B ) @ 
% 2.67/2.85           ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) ) ) ))).
% 2.67/2.85  thf('131', plain,
% 2.67/2.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.67/2.85         (((k4_xboole_0 @ X9 @ X11)
% 2.67/2.85            = (k2_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ 
% 2.67/2.85               (k3_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X11))))
% 2.67/2.85          | ~ (r1_tarski @ X11 @ X10))),
% 2.67/2.85      inference('cnf', [status(esa)], [t117_xboole_1])).
% 2.67/2.85  thf('132', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k4_xboole_0 @ X1 @ X0)
% 2.67/2.85           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 2.67/2.85              (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['130', '131'])).
% 2.67/2.85  thf('133', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['89', '90'])).
% 2.67/2.85  thf('134', plain,
% 2.67/2.85      (![X14 : $i]: ((k3_xboole_0 @ X14 @ k1_xboole_0) = (k1_xboole_0))),
% 2.67/2.85      inference('cnf', [status(esa)], [t2_boole])).
% 2.67/2.85  thf(commutativity_k2_xboole_0, axiom,
% 2.67/2.85    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 2.67/2.85  thf('135', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.67/2.85      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 2.67/2.85  thf('136', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k4_xboole_0 @ X1 @ X0)
% 2.67/2.85           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 2.67/2.85      inference('demod', [status(thm)], ['132', '133', '134', '135'])).
% 2.67/2.85  thf(t39_xboole_1, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.67/2.85  thf('137', plain,
% 2.67/2.85      (![X15 : $i, X16 : $i]:
% 2.67/2.85         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 2.67/2.85           = (k2_xboole_0 @ X15 @ X16))),
% 2.67/2.85      inference('cnf', [status(esa)], [t39_xboole_1])).
% 2.67/2.85  thf('138', plain,
% 2.67/2.85      (![X0 : $i]:
% 2.67/2.85         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['136', '137'])).
% 2.67/2.85  thf('139', plain, (![X17 : $i]: ((k4_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 2.67/2.85      inference('cnf', [status(esa)], [t3_boole])).
% 2.67/2.85  thf('140', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['138', '139'])).
% 2.67/2.85  thf('141', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         (((k4_subset_1 @ X0 @ k1_xboole_0 @ X1) = (X1))
% 2.67/2.85          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.67/2.85      inference('demod', [status(thm)], ['129', '140'])).
% 2.67/2.85  thf('142', plain,
% 2.67/2.85      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_D) = (sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['126', '141'])).
% 2.67/2.85  thf('143', plain,
% 2.67/2.85      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_D))
% 2.67/2.85          = (sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['120', '125', '142'])).
% 2.67/2.85  thf('144', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf('145', plain,
% 2.67/2.85      (![X54 : $i]:
% 2.67/2.85         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.67/2.85  thf('146', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('147', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.67/2.85        | ~ (l1_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['145', '146'])).
% 2.67/2.85  thf('148', plain, ((l1_struct_0 @ sk_A)),
% 2.67/2.85      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.85  thf('149', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.67/2.85      inference('demod', [status(thm)], ['147', '148'])).
% 2.67/2.85  thf('150', plain,
% 2.67/2.85      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 2.67/2.85          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 2.67/2.85              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 2.67/2.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 2.67/2.85      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.67/2.85  thf('151', plain,
% 2.67/2.85      (![X0 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.67/2.85          | ((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85              (k7_subset_1 @ (k2_struct_0 @ sk_A) @ X0 @ sk_C_1))
% 2.67/2.85              = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85                 (k3_subset_1 @ (k2_struct_0 @ sk_A) @ X0) @ sk_C_1)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['149', '150'])).
% 2.67/2.85  thf('152', plain,
% 2.67/2.85      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85         (k7_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0 @ sk_C_1))
% 2.67/2.85         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85            (k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0) @ sk_C_1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['144', '151'])).
% 2.67/2.85  thf('153', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['51', '52'])).
% 2.67/2.85  thf('154', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('155', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('156', plain,
% 2.67/2.85      (((k2_struct_0 @ sk_A)
% 2.67/2.85         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 2.67/2.85      inference('demod', [status(thm)], ['152', '153', '154', '155'])).
% 2.67/2.85  thf('157', plain,
% 2.67/2.85      (![X54 : $i]:
% 2.67/2.85         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.67/2.85  thf('158', plain,
% 2.67/2.85      (![X54 : $i]:
% 2.67/2.85         (((k2_struct_0 @ X54) = (u1_struct_0 @ X54)) | ~ (l1_struct_0 @ X54))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.67/2.85  thf('159', plain,
% 2.67/2.85      (![X50 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X50))),
% 2.67/2.85      inference('cnf', [status(esa)], [t4_subset_1])).
% 2.67/2.85  thf('160', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('161', plain,
% 2.67/2.85      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 2.67/2.85          | ((k3_subset_1 @ X48 @ (k7_subset_1 @ X48 @ X49 @ X47))
% 2.67/2.85              = (k4_subset_1 @ X48 @ (k3_subset_1 @ X48 @ X49) @ X47))
% 2.67/2.85          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X48)))),
% 2.67/2.85      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.67/2.85  thf('162', plain,
% 2.67/2.85      (![X0 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1))
% 2.67/2.85              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ sk_C_1)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['160', '161'])).
% 2.67/2.85  thf('163', plain,
% 2.67/2.85      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ sk_C_1))
% 2.67/2.85         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.67/2.85            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0) @ sk_C_1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['159', '162'])).
% 2.67/2.85  thf('164', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 2.67/2.85      inference('demod', [status(thm)], ['51', '52'])).
% 2.67/2.85  thf('165', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('166', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 2.67/2.85      inference('sup+', [status(thm)], ['56', '57'])).
% 2.67/2.85  thf('167', plain,
% 2.67/2.85      (((u1_struct_0 @ sk_A)
% 2.67/2.85         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 2.67/2.85      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 2.67/2.85  thf('168', plain,
% 2.67/2.85      ((((u1_struct_0 @ sk_A)
% 2.67/2.85          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 2.67/2.85        | ~ (l1_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['158', '167'])).
% 2.67/2.85  thf('169', plain, ((l1_struct_0 @ sk_A)),
% 2.67/2.85      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.85  thf('170', plain,
% 2.67/2.85      (((u1_struct_0 @ sk_A)
% 2.67/2.85         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ sk_C_1))),
% 2.67/2.85      inference('demod', [status(thm)], ['168', '169'])).
% 2.67/2.85  thf('171', plain,
% 2.67/2.85      ((((u1_struct_0 @ sk_A)
% 2.67/2.85          = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_C_1))
% 2.67/2.85        | ~ (l1_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['157', '170'])).
% 2.67/2.85  thf('172', plain, ((l1_struct_0 @ sk_A)),
% 2.67/2.85      inference('sup-', [status(thm)], ['42', '43'])).
% 2.67/2.85  thf('173', plain,
% 2.67/2.85      (((u1_struct_0 @ sk_A)
% 2.67/2.85         = (k4_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A) @ sk_C_1))),
% 2.67/2.85      inference('demod', [status(thm)], ['171', '172'])).
% 2.67/2.85  thf('174', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['156', '173'])).
% 2.67/2.85  thf('175', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['156', '173'])).
% 2.67/2.85  thf('176', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['156', '173'])).
% 2.67/2.85  thf('177', plain,
% 2.67/2.85      (![X0 : $i, X1 : $i]:
% 2.67/2.85         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 2.67/2.85      inference('sup-', [status(thm)], ['98', '99'])).
% 2.67/2.85  thf('178', plain,
% 2.67/2.85      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)
% 2.67/2.85          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['101', '102'])).
% 2.67/2.85  thf('179', plain,
% 2.67/2.85      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 2.67/2.85          (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_D)) = (sk_D)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)],
% 2.67/2.85                ['143', '174', '175', '176', '177', '178'])).
% 2.67/2.85  thf('180', plain,
% 2.67/2.85      ((((k1_tops_1 @ sk_A @ sk_D) = (sk_D)))
% 2.67/2.85         <= (((v3_pre_topc @ sk_D @ sk_A)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup+', [status(thm)], ['117', '179'])).
% 2.67/2.85  thf('181', plain,
% 2.67/2.85      (((r1_tarski @ sk_D @ sk_C_1)) <= (((r1_tarski @ sk_D @ sk_C_1)))),
% 2.67/2.85      inference('split', [status(esa)], ['2'])).
% 2.67/2.85  thf('182', plain,
% 2.67/2.85      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 2.67/2.85      inference('demod', [status(thm)], ['147', '148'])).
% 2.67/2.85  thf('183', plain,
% 2.67/2.85      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('split', [status(esa)], ['4'])).
% 2.67/2.85  thf(t48_tops_1, axiom,
% 2.67/2.85    (![A:$i]:
% 2.67/2.85     ( ( l1_pre_topc @ A ) =>
% 2.67/2.85       ( ![B:$i]:
% 2.67/2.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85           ( ![C:$i]:
% 2.67/2.85             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.67/2.85               ( ( r1_tarski @ B @ C ) =>
% 2.67/2.85                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.67/2.85  thf('184', plain,
% 2.67/2.85      (![X66 : $i, X67 : $i, X68 : $i]:
% 2.67/2.85         (~ (m1_subset_1 @ X66 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 2.67/2.85          | ~ (r1_tarski @ X66 @ X68)
% 2.67/2.85          | (r1_tarski @ (k1_tops_1 @ X67 @ X66) @ (k1_tops_1 @ X67 @ X68))
% 2.67/2.85          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (u1_struct_0 @ X67)))
% 2.67/2.85          | ~ (l1_pre_topc @ X67))),
% 2.67/2.85      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.67/2.85  thf('185', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (l1_pre_topc @ sk_A)
% 2.67/2.85           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 2.67/2.85           | ~ (r1_tarski @ sk_D @ X0)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['183', '184'])).
% 2.67/2.85  thf('186', plain, ((l1_pre_topc @ sk_A)),
% 2.67/2.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.67/2.85  thf('187', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.67/2.85           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 2.67/2.85           | ~ (r1_tarski @ sk_D @ X0)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['185', '186'])).
% 2.67/2.85  thf('188', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 2.67/2.85      inference('sup+', [status(thm)], ['156', '173'])).
% 2.67/2.85  thf('189', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 2.67/2.85           | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ X0))
% 2.67/2.85           | ~ (r1_tarski @ sk_D @ X0)))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('demod', [status(thm)], ['187', '188'])).
% 2.67/2.85  thf('190', plain,
% 2.67/2.85      (((~ (r1_tarski @ sk_D @ sk_C_1)
% 2.67/2.85         | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 2.67/2.85         <= (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['182', '189'])).
% 2.67/2.85  thf('191', plain,
% 2.67/2.85      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_D) @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 2.67/2.85         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['181', '190'])).
% 2.67/2.85  thf(d3_tarski, axiom,
% 2.67/2.85    (![A:$i,B:$i]:
% 2.67/2.85     ( ( r1_tarski @ A @ B ) <=>
% 2.67/2.85       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.67/2.85  thf('192', plain,
% 2.67/2.85      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.67/2.85         (~ (r2_hidden @ X2 @ X3)
% 2.67/2.85          | (r2_hidden @ X2 @ X4)
% 2.67/2.85          | ~ (r1_tarski @ X3 @ X4))),
% 2.67/2.85      inference('cnf', [status(esa)], [d3_tarski])).
% 2.67/2.85  thf('193', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          ((r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))
% 2.67/2.85           | ~ (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_D))))
% 2.67/2.85         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['191', '192'])).
% 2.67/2.85  thf('194', plain,
% 2.67/2.85      ((![X0 : $i]:
% 2.67/2.85          (~ (r2_hidden @ X0 @ sk_D)
% 2.67/2.85           | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C_1))))
% 2.67/2.85         <= (((r1_tarski @ sk_D @ sk_C_1)) & 
% 2.67/2.85             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['180', '193'])).
% 2.67/2.85  thf('195', plain,
% 2.67/2.85      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 2.67/2.85         <= (((r2_hidden @ sk_B @ sk_D)) & 
% 2.67/2.85             ((r1_tarski @ sk_D @ sk_C_1)) & 
% 2.67/2.85             ((v3_pre_topc @ sk_D @ sk_A)) & 
% 2.67/2.85             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))),
% 2.67/2.85      inference('sup-', [status(thm)], ['31', '194'])).
% 2.67/2.85  thf('196', plain,
% 2.67/2.85      ((~ (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))
% 2.67/2.85         <= (~ ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1))))),
% 2.67/2.85      inference('split', [status(esa)], ['6'])).
% 2.67/2.85  thf('197', plain,
% 2.67/2.85      (~ ((v3_pre_topc @ sk_D @ sk_A)) | 
% 2.67/2.85       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))) | 
% 2.67/2.85       ~ ((r1_tarski @ sk_D @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_D)) | 
% 2.67/2.85       ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C_1)))),
% 2.67/2.85      inference('sup-', [status(thm)], ['195', '196'])).
% 2.67/2.85  thf('198', plain, ($false),
% 2.67/2.85      inference('sat_resolution*', [status(thm)],
% 2.67/2.85                ['1', '3', '5', '7', '28', '30', '197'])).
% 2.67/2.85  
% 2.67/2.85  % SZS output end Refutation
% 2.67/2.85  
% 2.67/2.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
