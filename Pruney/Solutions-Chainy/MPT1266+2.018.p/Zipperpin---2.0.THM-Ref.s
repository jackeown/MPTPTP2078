%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JsKAQqj4U1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:14 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 812 expanded)
%              Number of leaves         :   32 ( 256 expanded)
%              Depth                    :   23
%              Number of atoms          : 1413 (7068 expanded)
%              Number of equality atoms :  105 ( 491 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t84_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tops_1 @ B @ A )
            <=> ( ( k1_tops_1 @ A @ B )
                = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t84_tops_1])).

thf('0',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v2_tops_1 @ X20 @ X21 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('15',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('17',plain,(
    ! [X15: $i] :
      ( ( l1_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','28'])).

thf('30',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('37',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('39',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v1_tops_1 @ X18 @ X19 )
      | ( ( k2_pre_topc @ X19 @ X18 )
        = ( k2_struct_0 @ X19 ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('41',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X13 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('52',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['3','52'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('59',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('60',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('61',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('65',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','67'])).

thf('72',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('78',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','76','77'])).

thf('79',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('82',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k3_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['2','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('85',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('88',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['83','88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k1_tops_1 @ X17 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ ( k2_pre_topc @ X17 @ ( k3_subset_1 @ ( u1_struct_0 @ X17 ) @ X16 ) ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('96',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['90','96'])).

thf('98',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','75'])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('105',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('106',plain,(
    ! [X12: $i] :
      ( ( ( k2_struct_0 @ X12 )
        = ( u1_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('108',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('109',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('111',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_subset_1 @ X5 @ X6 )
        = ( k4_xboole_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('112',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('115',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('116',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['113','116'])).

thf('118',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('120',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['105','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('123',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('125',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k2_pre_topc @ X19 @ X18 )
       != ( k2_struct_0 @ X19 ) )
      | ( v1_tops_1 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['123','128'])).

thf('130',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ X20 ) @ X21 )
      | ( v2_tops_1 @ X20 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('133',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('136',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('139',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','103','104','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JsKAQqj4U1
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:37:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 1045 iterations in 0.450s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.71/0.90  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.71/0.90  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.71/0.90  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.71/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.71/0.90  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.71/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.90  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.71/0.90  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.71/0.90  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.71/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.90  thf(t84_tops_1, conjecture,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( l1_pre_topc @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.90           ( ( v2_tops_1 @ B @ A ) <=>
% 0.71/0.90             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i]:
% 0.71/0.90        ( ( l1_pre_topc @ A ) =>
% 0.71/0.90          ( ![B:$i]:
% 0.71/0.90            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.90              ( ( v2_tops_1 @ B @ A ) <=>
% 0.71/0.90                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.71/0.90        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.71/0.90       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('split', [status(esa)], ['0'])).
% 0.71/0.90  thf(d3_struct_0, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X12 : $i]:
% 0.71/0.90         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X12 : $i]:
% 0.71/0.90         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('split', [status(esa)], ['4'])).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d4_tops_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( l1_pre_topc @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.90           ( ( v2_tops_1 @ B @ A ) <=>
% 0.71/0.90             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X20 : $i, X21 : $i]:
% 0.71/0.90         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.71/0.90          | ~ (v2_tops_1 @ X20 @ X21)
% 0.71/0.90          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.71/0.90          | ~ (l1_pre_topc @ X21))),
% 0.71/0.90      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.90        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.71/0.90        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['6', '7'])).
% 0.71/0.90  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d5_subset_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.90       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X5 : $i, X6 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.71/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X12 : $i]:
% 0.71/0.90         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.90      inference('sup+', [status(thm)], ['13', '14'])).
% 0.71/0.90  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(dt_l1_pre_topc, axiom,
% 0.71/0.90    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X15 : $i]: ((l1_struct_0 @ X15) | ~ (l1_pre_topc @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.71/0.90  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['15', '18'])).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['12', '19'])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X12 : $i]:
% 0.71/0.90         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.71/0.90        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.90      inference('sup+', [status(thm)], ['21', '22'])).
% 0.71/0.90  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['23', '24'])).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      (![X5 : $i, X6 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.71/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.71/0.90  thf('27', plain,
% 0.71/0.90      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.71/0.90  thf('28', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['20', '27'])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.71/0.90        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['8', '9', '28'])).
% 0.71/0.90  thf('30', plain,
% 0.71/0.90      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['5', '29'])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X12 : $i]:
% 0.71/0.90         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(dt_k3_subset_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.90       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.71/0.90          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['32', '33'])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.71/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.90        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.90      inference('sup+', [status(thm)], ['31', '34'])).
% 0.71/0.90  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['35', '36'])).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['25', '26'])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf(d3_tops_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( l1_pre_topc @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.90           ( ( v1_tops_1 @ B @ A ) <=>
% 0.71/0.90             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (![X18 : $i, X19 : $i]:
% 0.71/0.90         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.71/0.90          | ~ (v1_tops_1 @ X18 @ X19)
% 0.71/0.90          | ((k2_pre_topc @ X19 @ X18) = (k2_struct_0 @ X19))
% 0.71/0.90          | ~ (l1_pre_topc @ X19))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.90        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90            = (k2_struct_0 @ sk_A))
% 0.71/0.90        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['39', '40'])).
% 0.71/0.90  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90          = (k2_struct_0 @ sk_A))
% 0.71/0.90        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['41', '42'])).
% 0.71/0.90  thf('44', plain,
% 0.71/0.90      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90          = (k2_struct_0 @ sk_A)))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['30', '43'])).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf(dt_k2_pre_topc, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( l1_pre_topc @ A ) & 
% 0.71/0.90         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.71/0.90       ( m1_subset_1 @
% 0.71/0.90         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         (~ (l1_pre_topc @ X13)
% 0.71/0.90          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.71/0.90          | (m1_subset_1 @ (k2_pre_topc @ X13 @ X14) @ 
% 0.71/0.90             (k1_zfmisc_1 @ (u1_struct_0 @ X13))))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (((m1_subset_1 @ 
% 0.71/0.90         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.71/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.71/0.90        | ~ (l1_pre_topc @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.90  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      ((m1_subset_1 @ 
% 0.71/0.90        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['47', '48'])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.71/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['44', '49'])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      (![X5 : $i, X6 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.71/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.71/0.90  thf('52', plain,
% 0.71/0.90      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.71/0.90          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['50', '51'])).
% 0.71/0.90  thf('53', plain,
% 0.71/0.90      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.71/0.90           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.71/0.90         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['3', '52'])).
% 0.71/0.90  thf(t3_boole, axiom,
% 0.71/0.90    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.71/0.90  thf('54', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf(t48_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.71/0.90           = (k3_xboole_0 @ X2 @ X3))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['54', '55'])).
% 0.71/0.90  thf(t2_boole, axiom,
% 0.71/0.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.71/0.90  thf('58', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['56', '57'])).
% 0.71/0.90  thf(dt_k2_subset_1, axiom,
% 0.71/0.90    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.71/0.90  thf('59', plain,
% 0.71/0.90      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.71/0.90  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.71/0.90  thf('60', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 0.71/0.90      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.71/0.90  thf('61', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.71/0.90      inference('demod', [status(thm)], ['59', '60'])).
% 0.71/0.90  thf('62', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.71/0.90          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.71/0.90      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.71/0.90  thf('63', plain,
% 0.71/0.90      (![X0 : $i]: (m1_subset_1 @ (k3_subset_1 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['61', '62'])).
% 0.71/0.90  thf('64', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.71/0.90      inference('demod', [status(thm)], ['59', '60'])).
% 0.71/0.90  thf('65', plain,
% 0.71/0.90      (![X5 : $i, X6 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.71/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.71/0.90  thf('66', plain,
% 0.71/0.90      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['64', '65'])).
% 0.71/0.90  thf('67', plain,
% 0.71/0.90      (![X0 : $i]: (m1_subset_1 @ (k4_xboole_0 @ X0 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['63', '66'])).
% 0.71/0.90  thf('68', plain,
% 0.71/0.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['58', '67'])).
% 0.71/0.90  thf(involutiveness_k3_subset_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.71/0.90       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.71/0.90  thf('69', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.71/0.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.71/0.90  thf('70', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['68', '69'])).
% 0.71/0.90  thf('71', plain,
% 0.71/0.90      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['58', '67'])).
% 0.71/0.90  thf('72', plain,
% 0.71/0.90      (![X5 : $i, X6 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.71/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.71/0.90  thf('73', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['71', '72'])).
% 0.71/0.90  thf('74', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('75', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['73', '74'])).
% 0.71/0.90  thf('76', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['70', '75'])).
% 0.71/0.90  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.90  thf('78', plain,
% 0.71/0.90      ((((k1_xboole_0)
% 0.71/0.90          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['53', '76', '77'])).
% 0.71/0.90  thf('79', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.71/0.90           = (k3_xboole_0 @ X2 @ X3))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('80', plain,
% 0.71/0.90      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.71/0.90          = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['78', '79'])).
% 0.71/0.90  thf('81', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('82', plain,
% 0.71/0.90      ((((u1_struct_0 @ sk_A)
% 0.71/0.90          = (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['80', '81'])).
% 0.71/0.90  thf('83', plain,
% 0.71/0.90      (((((u1_struct_0 @ sk_A)
% 0.71/0.90           = (k3_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.71/0.90         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['2', '82'])).
% 0.71/0.90  thf('84', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['56', '57'])).
% 0.71/0.90  thf('85', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.71/0.90           = (k3_xboole_0 @ X2 @ X3))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('86', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['84', '85'])).
% 0.71/0.90  thf('87', plain, (![X1 : $i]: ((k4_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_boole])).
% 0.71/0.90  thf('88', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['86', '87'])).
% 0.71/0.90  thf('89', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.90  thf('90', plain,
% 0.71/0.90      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['83', '88', '89'])).
% 0.71/0.90  thf('91', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(d1_tops_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( l1_pre_topc @ A ) =>
% 0.71/0.90       ( ![B:$i]:
% 0.71/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.71/0.90           ( ( k1_tops_1 @ A @ B ) =
% 0.71/0.90             ( k3_subset_1 @
% 0.71/0.90               ( u1_struct_0 @ A ) @ 
% 0.71/0.90               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.71/0.90  thf('92', plain,
% 0.71/0.90      (![X16 : $i, X17 : $i]:
% 0.71/0.90         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.71/0.90          | ((k1_tops_1 @ X17 @ X16)
% 0.71/0.90              = (k3_subset_1 @ (u1_struct_0 @ X17) @ 
% 0.71/0.90                 (k2_pre_topc @ X17 @ (k3_subset_1 @ (u1_struct_0 @ X17) @ X16))))
% 0.71/0.90          | ~ (l1_pre_topc @ X17))),
% 0.71/0.90      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.71/0.90  thf('93', plain,
% 0.71/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.90        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.71/0.90            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90               (k2_pre_topc @ sk_A @ 
% 0.71/0.90                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['91', '92'])).
% 0.71/0.90  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('95', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['20', '27'])).
% 0.71/0.90  thf('96', plain,
% 0.71/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.71/0.90         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.71/0.90      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.71/0.90  thf('97', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.71/0.90          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.71/0.90             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['90', '96'])).
% 0.71/0.90  thf('98', plain,
% 0.71/0.90      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90          = (k2_struct_0 @ sk_A)))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['30', '43'])).
% 0.71/0.90  thf('99', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['70', '75'])).
% 0.71/0.90  thf('100', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.71/0.90         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.71/0.90  thf('101', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.71/0.90         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('split', [status(esa)], ['0'])).
% 0.71/0.90  thf('102', plain,
% 0.71/0.90      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.71/0.90         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.71/0.90             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['100', '101'])).
% 0.71/0.90  thf('103', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.71/0.90       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('simplify', [status(thm)], ['102'])).
% 0.71/0.90  thf('104', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.71/0.90       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('split', [status(esa)], ['4'])).
% 0.71/0.90  thf('105', plain,
% 0.71/0.90      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.71/0.90         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('split', [status(esa)], ['4'])).
% 0.71/0.90  thf('106', plain,
% 0.71/0.90      (![X12 : $i]:
% 0.71/0.90         (((k2_struct_0 @ X12) = (u1_struct_0 @ X12)) | ~ (l1_struct_0 @ X12))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.71/0.90  thf('107', plain,
% 0.71/0.90      ((m1_subset_1 @ 
% 0.71/0.90        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['47', '48'])).
% 0.71/0.90  thf('108', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.71/0.90          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.71/0.90      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.71/0.90  thf('109', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.71/0.90         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['107', '108'])).
% 0.71/0.90  thf('110', plain,
% 0.71/0.90      ((m1_subset_1 @ 
% 0.71/0.90        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['47', '48'])).
% 0.71/0.90  thf('111', plain,
% 0.71/0.90      (![X5 : $i, X6 : $i]:
% 0.71/0.90         (((k3_subset_1 @ X5 @ X6) = (k4_xboole_0 @ X5 @ X6))
% 0.71/0.90          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.71/0.90  thf('112', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.71/0.90         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['110', '111'])).
% 0.71/0.90  thf('113', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.71/0.90         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['109', '112'])).
% 0.71/0.90  thf('114', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.71/0.90         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['110', '111'])).
% 0.71/0.90  thf('115', plain,
% 0.71/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.71/0.90         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.71/0.90      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.71/0.90  thf('116', plain,
% 0.71/0.90      (((k1_tops_1 @ sk_A @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 0.71/0.90            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['114', '115'])).
% 0.71/0.90  thf('117', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.71/0.90         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['113', '116'])).
% 0.71/0.90  thf('118', plain,
% 0.71/0.90      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.71/0.90          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.71/0.90        | ~ (l1_struct_0 @ sk_A))),
% 0.71/0.90      inference('sup+', [status(thm)], ['106', '117'])).
% 0.71/0.90  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.71/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.90  thf('120', plain,
% 0.71/0.90      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B))
% 0.71/0.90         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.71/0.90      inference('demod', [status(thm)], ['118', '119'])).
% 0.71/0.90  thf('121', plain,
% 0.71/0.90      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.71/0.90          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.71/0.90         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('sup+', [status(thm)], ['105', '120'])).
% 0.71/0.90  thf('122', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['73', '74'])).
% 0.71/0.90  thf('123', plain,
% 0.71/0.90      ((((k2_struct_0 @ sk_A)
% 0.71/0.90          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.71/0.90         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('demod', [status(thm)], ['121', '122'])).
% 0.71/0.90  thf('124', plain,
% 0.71/0.90      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.71/0.90        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf('125', plain,
% 0.71/0.90      (![X18 : $i, X19 : $i]:
% 0.71/0.90         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.71/0.90          | ((k2_pre_topc @ X19 @ X18) != (k2_struct_0 @ X19))
% 0.71/0.90          | (v1_tops_1 @ X18 @ X19)
% 0.71/0.90          | ~ (l1_pre_topc @ X19))),
% 0.71/0.90      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.71/0.90  thf('126', plain,
% 0.71/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.90        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.71/0.90        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90            != (k2_struct_0 @ sk_A)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['124', '125'])).
% 0.71/0.90  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('128', plain,
% 0.71/0.90      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.71/0.90        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.71/0.90            != (k2_struct_0 @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['126', '127'])).
% 0.71/0.90  thf('129', plain,
% 0.71/0.90      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.71/0.90         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.71/0.90         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['123', '128'])).
% 0.71/0.90  thf('130', plain,
% 0.71/0.90      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.71/0.90         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('simplify', [status(thm)], ['129'])).
% 0.71/0.90  thf('131', plain,
% 0.71/0.90      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('132', plain,
% 0.71/0.90      (![X20 : $i, X21 : $i]:
% 0.71/0.90         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.71/0.90          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X21) @ X20) @ X21)
% 0.71/0.90          | (v2_tops_1 @ X20 @ X21)
% 0.71/0.90          | ~ (l1_pre_topc @ X21))),
% 0.71/0.90      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.71/0.90  thf('133', plain,
% 0.71/0.90      ((~ (l1_pre_topc @ sk_A)
% 0.71/0.90        | (v2_tops_1 @ sk_B @ sk_A)
% 0.71/0.90        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['131', '132'])).
% 0.71/0.90  thf('134', plain, ((l1_pre_topc @ sk_A)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('135', plain,
% 0.71/0.90      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.71/0.90         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.71/0.90      inference('demod', [status(thm)], ['20', '27'])).
% 0.71/0.90  thf('136', plain,
% 0.71/0.90      (((v2_tops_1 @ sk_B @ sk_A)
% 0.71/0.90        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['133', '134', '135'])).
% 0.71/0.90  thf('137', plain,
% 0.71/0.90      (((v2_tops_1 @ sk_B @ sk_A))
% 0.71/0.90         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['130', '136'])).
% 0.71/0.90  thf('138', plain,
% 0.71/0.90      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.71/0.90      inference('split', [status(esa)], ['0'])).
% 0.71/0.90  thf('139', plain,
% 0.71/0.90      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.71/0.90       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['137', '138'])).
% 0.71/0.90  thf('140', plain, ($false),
% 0.71/0.90      inference('sat_resolution*', [status(thm)], ['1', '103', '104', '139'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
