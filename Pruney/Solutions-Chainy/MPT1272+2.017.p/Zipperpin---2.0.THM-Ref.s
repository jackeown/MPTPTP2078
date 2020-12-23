%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aPyOgrNipk

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:31 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 150 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  759 (1419 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v2_tops_1 @ X35 @ X36 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X36 ) @ X35 ) @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( ( k1_tops_1 @ X45 @ X44 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X44 @ X45 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('9',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( l1_pre_topc @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( r1_tarski @ X41 @ X43 )
      | ( r1_tarski @ ( k1_tops_1 @ X42 @ X41 ) @ ( k1_tops_1 @ X42 @ X43 ) )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( r1_tarski @ X33 @ ( k2_pre_topc @ X34 @ X33 ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('25',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ sk_B_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('29',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ~ ( v2_tops_1 @ X44 @ X45 )
      | ( ( k1_tops_1 @ X45 @ X44 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X45 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('30',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v3_tops_1 @ X37 @ X38 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X38 @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('35',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_tops_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['32','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['22','27','39'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( r1_tarski @ X8 @ ( k3_subset_1 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ X10 @ ( k3_subset_1 @ X9 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X6 @ ( k3_subset_1 @ X6 @ X5 ) )
        = X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','53'])).

thf('55',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t40_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf('60',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t40_subset_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k3_subset_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['45','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','66'])).

thf('68',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( k1_xboole_0 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','67'])).

thf('69',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['6','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aPyOgrNipk
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:17:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.60/0.76  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.76  % Solved by: fo/fo7.sh
% 0.60/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.76  % done 575 iterations in 0.317s
% 0.60/0.76  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.76  % SZS output start Refutation
% 0.60/0.76  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.76  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.76  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.76  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.60/0.76  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.60/0.76  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.60/0.76  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.60/0.76  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.76  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.60/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.76  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.60/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.76  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.60/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.76  thf(t91_tops_1, conjecture,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( ( v3_tops_1 @ B @ A ) =>
% 0.60/0.76             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.60/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.76    (~( ![A:$i]:
% 0.60/0.76        ( ( l1_pre_topc @ A ) =>
% 0.60/0.76          ( ![B:$i]:
% 0.60/0.76            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76              ( ( v3_tops_1 @ B @ A ) =>
% 0.60/0.76                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 0.60/0.76    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 0.60/0.76  thf('0', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(d4_tops_1, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( ( v2_tops_1 @ B @ A ) <=>
% 0.60/0.76             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.60/0.76  thf('1', plain,
% 0.60/0.76      (![X35 : $i, X36 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.60/0.76          | ~ (v2_tops_1 @ X35 @ X36)
% 0.60/0.76          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X36) @ X35) @ X36)
% 0.60/0.76          | ~ (l1_pre_topc @ X36))),
% 0.60/0.76      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.60/0.76  thf('2', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.60/0.76        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.76  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('4', plain,
% 0.60/0.76      (((v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.60/0.76        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.60/0.76      inference('demod', [status(thm)], ['2', '3'])).
% 0.60/0.76  thf('5', plain,
% 0.60/0.76      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('6', plain, (~ (v2_tops_1 @ sk_B_1 @ sk_A)),
% 0.60/0.76      inference('clc', [status(thm)], ['4', '5'])).
% 0.60/0.76  thf('7', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(t84_tops_1, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( ( v2_tops_1 @ B @ A ) <=>
% 0.60/0.76             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.60/0.76  thf('8', plain,
% 0.60/0.76      (![X44 : $i, X45 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.60/0.76          | ((k1_tops_1 @ X45 @ X44) != (k1_xboole_0))
% 0.60/0.76          | (v2_tops_1 @ X44 @ X45)
% 0.60/0.76          | ~ (l1_pre_topc @ X45))),
% 0.60/0.76      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.60/0.76  thf('9', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.60/0.76        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.76  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('11', plain,
% 0.60/0.76      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.60/0.76        | ((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.60/0.76      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.76  thf('12', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(dt_k2_pre_topc, axiom,
% 0.60/0.76    (![A:$i,B:$i]:
% 0.60/0.76     ( ( ( l1_pre_topc @ A ) & 
% 0.60/0.76         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.60/0.76       ( m1_subset_1 @
% 0.60/0.76         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.76  thf('13', plain,
% 0.60/0.76      (![X31 : $i, X32 : $i]:
% 0.60/0.76         (~ (l1_pre_topc @ X31)
% 0.60/0.76          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 0.60/0.76          | (m1_subset_1 @ (k2_pre_topc @ X31 @ X32) @ 
% 0.60/0.76             (k1_zfmisc_1 @ (u1_struct_0 @ X31))))),
% 0.60/0.76      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.60/0.76  thf('14', plain,
% 0.60/0.76      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.60/0.76         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.76        | ~ (l1_pre_topc @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.76  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('16', plain,
% 0.60/0.76      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.60/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['14', '15'])).
% 0.60/0.76  thf('17', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(t48_tops_1, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( ![C:$i]:
% 0.60/0.76             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76               ( ( r1_tarski @ B @ C ) =>
% 0.60/0.76                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.60/0.76  thf('18', plain,
% 0.60/0.76      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.60/0.76          | ~ (r1_tarski @ X41 @ X43)
% 0.60/0.76          | (r1_tarski @ (k1_tops_1 @ X42 @ X41) @ (k1_tops_1 @ X42 @ X43))
% 0.60/0.76          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 0.60/0.76          | ~ (l1_pre_topc @ X42))),
% 0.60/0.76      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.60/0.76  thf('19', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (~ (l1_pre_topc @ sk_A)
% 0.60/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.76          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.60/0.76          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.76  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('21', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.60/0.76          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ (k1_tops_1 @ sk_A @ X0))
% 0.60/0.76          | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.60/0.76      inference('demod', [status(thm)], ['19', '20'])).
% 0.60/0.76  thf('22', plain,
% 0.60/0.76      ((~ (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))
% 0.60/0.76        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.60/0.76           (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_1))))),
% 0.60/0.76      inference('sup-', [status(thm)], ['16', '21'])).
% 0.60/0.76  thf('23', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(t48_pre_topc, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.60/0.76  thf('24', plain,
% 0.60/0.76      (![X33 : $i, X34 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.60/0.76          | (r1_tarski @ X33 @ (k2_pre_topc @ X34 @ X33))
% 0.60/0.76          | ~ (l1_pre_topc @ X34))),
% 0.60/0.76      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.60/0.76  thf('25', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | (r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.76  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('27', plain, ((r1_tarski @ sk_B_1 @ (k2_pre_topc @ sk_A @ sk_B_1))),
% 0.60/0.76      inference('demod', [status(thm)], ['25', '26'])).
% 0.60/0.76  thf('28', plain,
% 0.60/0.76      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ 
% 0.60/0.76        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('demod', [status(thm)], ['14', '15'])).
% 0.60/0.76  thf('29', plain,
% 0.60/0.76      (![X44 : $i, X45 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 0.60/0.76          | ~ (v2_tops_1 @ X44 @ X45)
% 0.60/0.76          | ((k1_tops_1 @ X45 @ X44) = (k1_xboole_0))
% 0.60/0.76          | ~ (l1_pre_topc @ X45))),
% 0.60/0.76      inference('cnf', [status(esa)], [t84_tops_1])).
% 0.60/0.76  thf('30', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_1)) = (k1_xboole_0))
% 0.60/0.76        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.76  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('32', plain,
% 0.60/0.76      ((((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_1)) = (k1_xboole_0))
% 0.60/0.76        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A))),
% 0.60/0.76      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.76  thf('33', plain,
% 0.60/0.76      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf(d5_tops_1, axiom,
% 0.60/0.76    (![A:$i]:
% 0.60/0.76     ( ( l1_pre_topc @ A ) =>
% 0.60/0.76       ( ![B:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.76           ( ( v3_tops_1 @ B @ A ) <=>
% 0.60/0.76             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 0.60/0.76  thf('34', plain,
% 0.60/0.76      (![X37 : $i, X38 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.60/0.76          | ~ (v3_tops_1 @ X37 @ X38)
% 0.60/0.76          | (v2_tops_1 @ (k2_pre_topc @ X38 @ X37) @ X38)
% 0.60/0.76          | ~ (l1_pre_topc @ X38))),
% 0.60/0.76      inference('cnf', [status(esa)], [d5_tops_1])).
% 0.60/0.76  thf('35', plain,
% 0.60/0.76      ((~ (l1_pre_topc @ sk_A)
% 0.60/0.76        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A)
% 0.60/0.76        | ~ (v3_tops_1 @ sk_B_1 @ sk_A))),
% 0.60/0.76      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.76  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('37', plain, ((v3_tops_1 @ sk_B_1 @ sk_A)),
% 0.60/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.76  thf('38', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B_1) @ sk_A)),
% 0.60/0.76      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.60/0.76  thf('39', plain,
% 0.60/0.76      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['32', '38'])).
% 0.60/0.76  thf('40', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B_1) @ k1_xboole_0)),
% 0.60/0.76      inference('demod', [status(thm)], ['22', '27', '39'])).
% 0.60/0.76  thf(t4_subset_1, axiom,
% 0.60/0.76    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.76  thf('41', plain,
% 0.60/0.76      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf(dt_k3_subset_1, axiom,
% 0.60/0.76    (![A:$i,B:$i]:
% 0.60/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.76       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.76  thf('42', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.60/0.76          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.60/0.76      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.60/0.76  thf('43', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.76  thf(t3_subset, axiom,
% 0.60/0.76    (![A:$i,B:$i]:
% 0.60/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.60/0.76  thf('44', plain,
% 0.60/0.76      (![X25 : $i, X26 : $i]:
% 0.60/0.76         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.60/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.76  thf('45', plain,
% 0.60/0.76      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)),
% 0.60/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.76  thf('46', plain,
% 0.60/0.76      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf('47', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.76  thf(t35_subset_1, axiom,
% 0.60/0.76    (![A:$i,B:$i]:
% 0.60/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.76       ( ![C:$i]:
% 0.60/0.76         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.76           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.60/0.76             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.76  thf('48', plain,
% 0.60/0.76      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.60/0.76          | (r1_tarski @ X8 @ (k3_subset_1 @ X9 @ X10))
% 0.60/0.76          | ~ (r1_tarski @ X10 @ (k3_subset_1 @ X9 @ X8))
% 0.60/0.76          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.60/0.76      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.60/0.76  thf('49', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.60/0.76          | ~ (r1_tarski @ X1 @ 
% 0.60/0.76               (k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)))
% 0.60/0.76          | (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 0.60/0.76             (k3_subset_1 @ X0 @ X1)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.76  thf('50', plain,
% 0.60/0.76      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf(involutiveness_k3_subset_1, axiom,
% 0.60/0.76    (![A:$i,B:$i]:
% 0.60/0.76     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.76       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.60/0.76  thf('51', plain,
% 0.60/0.76      (![X5 : $i, X6 : $i]:
% 0.60/0.76         (((k3_subset_1 @ X6 @ (k3_subset_1 @ X6 @ X5)) = (X5))
% 0.60/0.76          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.60/0.76      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.60/0.76  thf('52', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.76  thf('53', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.60/0.76          | ~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.60/0.76          | (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 0.60/0.76             (k3_subset_1 @ X0 @ X1)))),
% 0.60/0.76      inference('demod', [status(thm)], ['49', '52'])).
% 0.60/0.76  thf('54', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         ((r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 0.60/0.76           (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.60/0.76          | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['46', '53'])).
% 0.60/0.76  thf('55', plain,
% 0.60/0.76      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf('56', plain,
% 0.60/0.76      (![X25 : $i, X26 : $i]:
% 0.60/0.76         ((r1_tarski @ X25 @ X26) | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26)))),
% 0.60/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.60/0.76  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.76      inference('sup-', [status(thm)], ['55', '56'])).
% 0.60/0.76  thf('58', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ 
% 0.60/0.76          (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.60/0.76      inference('demod', [status(thm)], ['54', '57'])).
% 0.60/0.76  thf('59', plain,
% 0.60/0.76      (![X24 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X24))),
% 0.60/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.76  thf(t40_subset_1, axiom,
% 0.60/0.76    (![A:$i,B:$i,C:$i]:
% 0.60/0.76     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.76       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.60/0.76         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.76  thf('60', plain,
% 0.60/0.76      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.60/0.76         (((X11) = (k1_xboole_0))
% 0.60/0.76          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.60/0.76          | ~ (r1_tarski @ X11 @ (k3_subset_1 @ X13 @ X12))
% 0.60/0.76          | ~ (r1_tarski @ X11 @ X12))),
% 0.60/0.76      inference('cnf', [status(esa)], [t40_subset_1])).
% 0.60/0.76  thf('61', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.60/0.76          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.60/0.76          | ((X1) = (k1_xboole_0)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.76  thf('62', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (((k3_subset_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.60/0.76          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['58', '61'])).
% 0.60/0.76  thf('63', plain,
% 0.60/0.76      (((k3_subset_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['45', '62'])).
% 0.60/0.76  thf('64', plain,
% 0.60/0.76      (![X0 : $i, X1 : $i]:
% 0.60/0.76         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.60/0.76          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.60/0.76          | ((X1) = (k1_xboole_0)))),
% 0.60/0.76      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.76  thf('65', plain,
% 0.60/0.76      (![X0 : $i]:
% 0.60/0.76         (~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.60/0.76          | ((X0) = (k1_xboole_0))
% 0.60/0.76          | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['63', '64'])).
% 0.60/0.76  thf('66', plain,
% 0.60/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.60/0.76      inference('simplify', [status(thm)], ['65'])).
% 0.60/0.76  thf('67', plain, (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.60/0.76      inference('sup-', [status(thm)], ['40', '66'])).
% 0.60/0.76  thf('68', plain,
% 0.60/0.76      (((v2_tops_1 @ sk_B_1 @ sk_A) | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.60/0.76      inference('demod', [status(thm)], ['11', '67'])).
% 0.60/0.76  thf('69', plain, ((v2_tops_1 @ sk_B_1 @ sk_A)),
% 0.60/0.76      inference('simplify', [status(thm)], ['68'])).
% 0.60/0.76  thf('70', plain, ($false), inference('demod', [status(thm)], ['6', '69'])).
% 0.60/0.76  
% 0.60/0.76  % SZS output end Refutation
% 0.60/0.76  
% 0.62/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
