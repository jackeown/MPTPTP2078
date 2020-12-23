%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZFN3ISdAj9

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:39 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 296 expanded)
%              Number of leaves         :   33 ( 104 expanded)
%              Depth                    :   17
%              Number of atoms          : 1009 (2685 expanded)
%              Number of equality atoms :   54 ( 168 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(t97_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tops_1 @ B @ A ) )
           => ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( ( v3_pre_topc @ B @ A )
                & ( v3_tops_1 @ B @ A ) )
             => ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X5 @ X6 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('9',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('11',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('13',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('18',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','5'])).

thf('26',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['15','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( v3_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('36',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['6','37'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v3_pre_topc @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('44',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X4 ) @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('45',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('46',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ( v4_pre_topc @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('53',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v3_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X14 )
      | ( ( k2_pre_topc @ X14 @ X13 )
        = X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('67',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('68',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('73',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc3_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_tops_1 @ B @ A ) ) ) ) )).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v3_tops_1 @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc3_tops_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v3_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v3_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_tops_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ( v3_tops_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( v3_tops_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    v3_tops_1 @ k1_xboole_0 @ sk_A ),
    inference('sup+',[status(thm)],['70','81'])).

thf('83',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('84',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) @ X26 )
      | ~ ( v3_tops_1 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[t91_tops_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v3_tops_1 @ k1_xboole_0 @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_tops_1 @ ( u1_struct_0 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('92',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['90','93'])).

thf('95',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['65','96'])).

thf('98',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','56'])).

thf('102',plain,(
    k1_xboole_0 = sk_B ),
    inference(demod,[status(thm)],['38','100','101'])).

thf('103',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZFN3ISdAj9
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 237 iterations in 0.087s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.36/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.36/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.36/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.36/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.36/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.36/0.55  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 0.36/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.36/0.55  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.36/0.55  thf(t97_tops_1, conjecture,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.36/0.55             ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i]:
% 0.36/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55          ( ![B:$i]:
% 0.36/0.55            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55              ( ( ( v3_pre_topc @ B @ A ) & ( v3_tops_1 @ B @ A ) ) =>
% 0.36/0.55                ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t97_tops_1])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.36/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(d5_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.36/0.55  thf('4', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.36/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.36/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(dt_k3_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.36/0.55  thf('8', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i]:
% 0.36/0.55         ((m1_subset_1 @ (k3_subset_1 @ X5 @ X6) @ (k1_zfmisc_1 @ X5))
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.36/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('11', plain,
% 0.36/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf(d3_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v1_tops_1 @ B @ A ) <=>
% 0.36/0.55             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.55          | ~ (v1_tops_1 @ X19 @ X20)
% 0.36/0.55          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.36/0.55          | ~ (l1_pre_topc @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55            = (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.36/0.55  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55          = (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['13', '14'])).
% 0.36/0.55  thf('16', plain,
% 0.36/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf(t52_pre_topc, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.36/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.36/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.55          | ~ (v4_pre_topc @ X13 @ X14)
% 0.36/0.55          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.36/0.55          | ~ (l1_pre_topc @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55            = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.55  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('20', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55        | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['18', '19'])).
% 0.36/0.55  thf('21', plain,
% 0.36/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.36/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf(t29_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.36/0.55             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.55          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.36/0.55          | (v4_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.55  thf('23', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.36/0.55        | ~ (v3_pre_topc @ 
% 0.36/0.55             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55              (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.36/0.55             sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.36/0.55  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.36/0.55         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.36/0.55  thf('26', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      ((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.36/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['20', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['15', '28'])).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(t91_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( l1_pre_topc @ A ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v3_tops_1 @ B @ A ) =>
% 0.36/0.55             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.36/0.55  thf('31', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.55          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 0.36/0.55          | ~ (v3_tops_1 @ X25 @ X26)
% 0.36/0.55          | ~ (l1_pre_topc @ X26))),
% 0.36/0.55      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      ((~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ~ (v3_tops_1 @ sk_B @ sk_A)
% 0.36/0.55        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.55  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('34', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.36/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.36/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.36/0.55  thf('37', plain,
% 0.36/0.55      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['29', '36'])).
% 0.36/0.55  thf('38', plain,
% 0.36/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['6', '37'])).
% 0.36/0.55  thf(t4_subset_1, axiom,
% 0.36/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.55  thf('39', plain,
% 0.36/0.55      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf(cc1_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('40', plain,
% 0.36/0.55      (![X15 : $i, X16 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.36/0.55          | (v3_pre_topc @ X15 @ X16)
% 0.36/0.55          | ~ (v1_xboole_0 @ X15)
% 0.36/0.55          | ~ (l1_pre_topc @ X16)
% 0.36/0.55          | ~ (v2_pre_topc @ X16))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_tops_1])).
% 0.36/0.55  thf('41', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.55          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.36/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.36/0.55  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('43', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['41', '42'])).
% 0.36/0.55  thf(dt_k2_subset_1, axiom,
% 0.36/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.55  thf('44', plain,
% 0.36/0.55      (![X4 : $i]: (m1_subset_1 @ (k2_subset_1 @ X4) @ (k1_zfmisc_1 @ X4))),
% 0.36/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.36/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.36/0.55  thf('45', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.36/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.36/0.55  thf('46', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('47', plain,
% 0.36/0.55      (![X21 : $i, X22 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.36/0.55          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.36/0.55          | (v4_pre_topc @ X21 @ X22)
% 0.36/0.55          | ~ (l1_pre_topc @ X22))),
% 0.36/0.55      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.36/0.55  thf('48', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.55          | ~ (v3_pre_topc @ 
% 0.36/0.55               (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0)) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.55  thf('49', plain,
% 0.36/0.55      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf('50', plain,
% 0.36/0.55      (![X7 : $i, X8 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.36/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.36/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.36/0.55  thf('51', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['49', '50'])).
% 0.36/0.55  thf('52', plain,
% 0.36/0.55      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf('53', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.36/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.55  thf('54', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['52', '53'])).
% 0.36/0.55  thf(t3_boole, axiom,
% 0.36/0.55    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.36/0.55  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.55      inference('cnf', [status(esa)], [t3_boole])).
% 0.36/0.55  thf('56', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.55  thf('57', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['51', '56'])).
% 0.36/0.55  thf('58', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.55          | ~ (v3_pre_topc @ k1_xboole_0 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['48', '57'])).
% 0.36/0.55  thf('59', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | (v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['43', '58'])).
% 0.36/0.55  thf('60', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((v4_pre_topc @ (u1_struct_0 @ X0) @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['59'])).
% 0.36/0.55  thf('61', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('62', plain,
% 0.36/0.55      (![X13 : $i, X14 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.36/0.55          | ~ (v4_pre_topc @ X13 @ X14)
% 0.36/0.55          | ((k2_pre_topc @ X14 @ X13) = (X13))
% 0.36/0.55          | ~ (l1_pre_topc @ X14))),
% 0.36/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.36/0.55  thf('63', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (v4_pre_topc @ (u1_struct_0 @ X0) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['61', '62'])).
% 0.36/0.55  thf('64', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['60', '63'])).
% 0.36/0.55  thf('65', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.36/0.55          | ~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0))),
% 0.36/0.55      inference('simplify', [status(thm)], ['64'])).
% 0.36/0.55  thf('66', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['51', '56'])).
% 0.36/0.55  thf('67', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('68', plain,
% 0.36/0.55      (![X2 : $i, X3 : $i]:
% 0.36/0.55         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.36/0.55          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.36/0.55  thf('69', plain,
% 0.36/0.55      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['67', '68'])).
% 0.36/0.55  thf('70', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['66', '69'])).
% 0.36/0.55  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('72', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.36/0.55      inference('sup+', [status(thm)], ['66', '69'])).
% 0.36/0.55  thf('73', plain,
% 0.36/0.55      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf(cc3_tops_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.36/0.55           ( ( v1_xboole_0 @ B ) => ( v3_tops_1 @ B @ A ) ) ) ) ))).
% 0.36/0.55  thf('74', plain,
% 0.36/0.55      (![X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.36/0.55          | (v3_tops_1 @ X17 @ X18)
% 0.36/0.55          | ~ (v1_xboole_0 @ X17)
% 0.36/0.55          | ~ (l1_pre_topc @ X18)
% 0.36/0.55          | ~ (v2_pre_topc @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc3_tops_1])).
% 0.36/0.55  thf('75', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.55          | (v3_tops_1 @ k1_xboole_0 @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['73', '74'])).
% 0.36/0.55  thf('76', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.36/0.55  thf('77', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ X0)
% 0.36/0.55          | ~ (l1_pre_topc @ X0)
% 0.36/0.55          | (v3_tops_1 @ k1_xboole_0 @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.36/0.55  thf('78', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i]:
% 0.36/0.55         ((v3_tops_1 @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.36/0.55          | ~ (l1_pre_topc @ X1)
% 0.36/0.55          | ~ (v2_pre_topc @ X1))),
% 0.36/0.55      inference('sup+', [status(thm)], ['72', '77'])).
% 0.36/0.55  thf('79', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (v2_pre_topc @ sk_A) | (v3_tops_1 @ (k4_xboole_0 @ X0 @ X0) @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['71', '78'])).
% 0.36/0.55  thf('80', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('81', plain, (![X0 : $i]: (v3_tops_1 @ (k4_xboole_0 @ X0 @ X0) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['79', '80'])).
% 0.36/0.55  thf('82', plain, ((v3_tops_1 @ k1_xboole_0 @ sk_A)),
% 0.36/0.55      inference('sup+', [status(thm)], ['70', '81'])).
% 0.36/0.55  thf('83', plain,
% 0.36/0.55      (![X9 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.55  thf('84', plain,
% 0.36/0.55      (![X25 : $i, X26 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.36/0.55          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25) @ X26)
% 0.36/0.55          | ~ (v3_tops_1 @ X25 @ X26)
% 0.36/0.55          | ~ (l1_pre_topc @ X26))),
% 0.36/0.55      inference('cnf', [status(esa)], [t91_tops_1])).
% 0.36/0.55  thf('85', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.36/0.55          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['83', '84'])).
% 0.36/0.55  thf('86', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['54', '55'])).
% 0.36/0.55  thf('87', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ~ (v3_tops_1 @ k1_xboole_0 @ X0)
% 0.36/0.55          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.36/0.55      inference('demod', [status(thm)], ['85', '86'])).
% 0.36/0.55  thf('88', plain,
% 0.36/0.55      (((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['82', '87'])).
% 0.36/0.55  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('90', plain, ((v1_tops_1 @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.36/0.55      inference('demod', [status(thm)], ['88', '89'])).
% 0.36/0.55  thf('91', plain, (![X4 : $i]: (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X4))),
% 0.36/0.55      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.55  thf('92', plain,
% 0.36/0.55      (![X19 : $i, X20 : $i]:
% 0.36/0.55         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.36/0.55          | ~ (v1_tops_1 @ X19 @ X20)
% 0.36/0.55          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.36/0.55          | ~ (l1_pre_topc @ X20))),
% 0.36/0.55      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.36/0.55  thf('93', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         (~ (l1_pre_topc @ X0)
% 0.36/0.55          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.36/0.55          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.36/0.55      inference('sup-', [status(thm)], ['91', '92'])).
% 0.36/0.55  thf('94', plain,
% 0.36/0.55      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup-', [status(thm)], ['90', '93'])).
% 0.36/0.55  thf('95', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('96', plain,
% 0.36/0.55      (((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['94', '95'])).
% 0.36/0.55  thf('97', plain,
% 0.36/0.55      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))
% 0.36/0.55        | ~ (l1_pre_topc @ sk_A)
% 0.36/0.55        | ~ (v2_pre_topc @ sk_A))),
% 0.36/0.55      inference('sup+', [status(thm)], ['65', '96'])).
% 0.36/0.55  thf('98', plain, ((l1_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('99', plain, ((v2_pre_topc @ sk_A)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('100', plain, (((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.36/0.55  thf('101', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.36/0.55      inference('demod', [status(thm)], ['51', '56'])).
% 0.36/0.55  thf('102', plain, (((k1_xboole_0) = (sk_B))),
% 0.36/0.55      inference('demod', [status(thm)], ['38', '100', '101'])).
% 0.36/0.55  thf('103', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('104', plain, ($false),
% 0.36/0.55      inference('simplify_reflect-', [status(thm)], ['102', '103'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
