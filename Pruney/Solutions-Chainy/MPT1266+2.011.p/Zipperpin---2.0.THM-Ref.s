%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6xVZjf6yeQ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:13 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  182 (1472 expanded)
%              Number of leaves         :   28 ( 440 expanded)
%              Depth                    :   28
%              Number of atoms          : 1616 (14114 expanded)
%              Number of equality atoms :  120 ( 937 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('7',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('13',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('14',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('28',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','27'])).

thf('29',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('34',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('40',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('43',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
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
    inference('sup+',[status(thm)],['2','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('56',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['54'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('61',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('64',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','59','62','63'])).

thf('65',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('71',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('72',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('78',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['11','18'])).

thf('81',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('83',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['75','83'])).

thf('85',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','41'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('88',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('93',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('95',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('98',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('100',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','100'])).

thf('102',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,
    ( ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('106',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['101'])).

thf('108',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('114',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('116',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('119',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('121',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('124',plain,
    ( ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','110'])).

thf('126',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('127',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('128',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('130',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['125','130'])).

thf('132',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['124','131'])).

thf('133',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','132'])).

thf('134',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('135',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('136',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
       != ( k2_struct_0 @ X20 ) )
      | ( v1_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('138',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['133','140'])).

thf('142',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('145',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['19','26'])).

thf('148',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['142','148'])).

thf('150',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('151',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','91','92','151'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6xVZjf6yeQ
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.43/1.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.43/1.68  % Solved by: fo/fo7.sh
% 1.43/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.68  % done 3882 iterations in 1.223s
% 1.43/1.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.43/1.68  % SZS output start Refutation
% 1.43/1.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.43/1.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.43/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.43/1.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.43/1.68  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 1.43/1.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.43/1.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.43/1.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.43/1.68  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.43/1.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.43/1.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.43/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.43/1.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.43/1.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.43/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.43/1.68  thf(t84_tops_1, conjecture,
% 1.43/1.68    (![A:$i]:
% 1.43/1.68     ( ( l1_pre_topc @ A ) =>
% 1.43/1.68       ( ![B:$i]:
% 1.43/1.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.68           ( ( v2_tops_1 @ B @ A ) <=>
% 1.43/1.68             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.43/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.68    (~( ![A:$i]:
% 1.43/1.68        ( ( l1_pre_topc @ A ) =>
% 1.43/1.68          ( ![B:$i]:
% 1.43/1.68            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.68              ( ( v2_tops_1 @ B @ A ) <=>
% 1.43/1.68                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.43/1.68    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 1.43/1.68  thf('0', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 1.43/1.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('1', plain,
% 1.43/1.68      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.43/1.68       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('split', [status(esa)], ['0'])).
% 1.43/1.68  thf(d3_struct_0, axiom,
% 1.43/1.68    (![A:$i]:
% 1.43/1.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.43/1.68  thf('2', plain,
% 1.43/1.68      (![X13 : $i]:
% 1.43/1.68         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.43/1.68  thf('3', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('4', plain,
% 1.43/1.68      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('split', [status(esa)], ['3'])).
% 1.43/1.68  thf('5', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf(d4_tops_1, axiom,
% 1.43/1.68    (![A:$i]:
% 1.43/1.68     ( ( l1_pre_topc @ A ) =>
% 1.43/1.68       ( ![B:$i]:
% 1.43/1.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.68           ( ( v2_tops_1 @ B @ A ) <=>
% 1.43/1.68             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 1.43/1.68  thf('6', plain,
% 1.43/1.68      (![X21 : $i, X22 : $i]:
% 1.43/1.68         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.43/1.68          | ~ (v2_tops_1 @ X21 @ X22)
% 1.43/1.68          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 1.43/1.68          | ~ (l1_pre_topc @ X22))),
% 1.43/1.68      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.43/1.68  thf('7', plain,
% 1.43/1.68      ((~ (l1_pre_topc @ sk_A)
% 1.43/1.68        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.43/1.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['5', '6'])).
% 1.43/1.68  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('9', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf(d5_subset_1, axiom,
% 1.43/1.68    (![A:$i,B:$i]:
% 1.43/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.43/1.68       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.43/1.68  thf('10', plain,
% 1.43/1.68      (![X6 : $i, X7 : $i]:
% 1.43/1.68         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 1.43/1.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.43/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.43/1.68  thf('11', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['9', '10'])).
% 1.43/1.68  thf('12', plain,
% 1.43/1.68      (![X13 : $i]:
% 1.43/1.68         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.43/1.68  thf('13', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['9', '10'])).
% 1.43/1.68  thf('14', plain,
% 1.43/1.68      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68        | ~ (l1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup+', [status(thm)], ['12', '13'])).
% 1.43/1.68  thf('15', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf(dt_l1_pre_topc, axiom,
% 1.43/1.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.43/1.68  thf('16', plain,
% 1.43/1.68      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 1.43/1.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.43/1.68  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 1.43/1.68      inference('sup-', [status(thm)], ['15', '16'])).
% 1.43/1.68  thf('18', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('demod', [status(thm)], ['14', '17'])).
% 1.43/1.68  thf('19', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('demod', [status(thm)], ['11', '18'])).
% 1.43/1.68  thf('20', plain,
% 1.43/1.68      (![X13 : $i]:
% 1.43/1.68         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.43/1.68  thf('21', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('22', plain,
% 1.43/1.68      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 1.43/1.68        | ~ (l1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup+', [status(thm)], ['20', '21'])).
% 1.43/1.68  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 1.43/1.68      inference('sup-', [status(thm)], ['15', '16'])).
% 1.43/1.68  thf('24', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['22', '23'])).
% 1.43/1.68  thf('25', plain,
% 1.43/1.68      (![X6 : $i, X7 : $i]:
% 1.43/1.68         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 1.43/1.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.43/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.43/1.68  thf('26', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['24', '25'])).
% 1.43/1.68  thf('27', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('demod', [status(thm)], ['19', '26'])).
% 1.43/1.68  thf('28', plain,
% 1.43/1.68      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.43/1.68        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('demod', [status(thm)], ['7', '8', '27'])).
% 1.43/1.68  thf('29', plain,
% 1.43/1.68      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['4', '28'])).
% 1.43/1.68  thf('30', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf(dt_k3_subset_1, axiom,
% 1.43/1.68    (![A:$i,B:$i]:
% 1.43/1.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.43/1.68       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.43/1.68  thf('31', plain,
% 1.43/1.68      (![X8 : $i, X9 : $i]:
% 1.43/1.68         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 1.43/1.68          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 1.43/1.68      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.43/1.68  thf('32', plain,
% 1.43/1.68      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['30', '31'])).
% 1.43/1.68  thf('33', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('demod', [status(thm)], ['11', '18'])).
% 1.43/1.68  thf('34', plain,
% 1.43/1.68      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['32', '33'])).
% 1.43/1.68  thf(d3_tops_1, axiom,
% 1.43/1.68    (![A:$i]:
% 1.43/1.68     ( ( l1_pre_topc @ A ) =>
% 1.43/1.68       ( ![B:$i]:
% 1.43/1.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.68           ( ( v1_tops_1 @ B @ A ) <=>
% 1.43/1.68             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 1.43/1.68  thf('35', plain,
% 1.43/1.68      (![X19 : $i, X20 : $i]:
% 1.43/1.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.43/1.68          | ~ (v1_tops_1 @ X19 @ X20)
% 1.43/1.68          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 1.43/1.68          | ~ (l1_pre_topc @ X20))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.43/1.68  thf('36', plain,
% 1.43/1.68      ((~ (l1_pre_topc @ sk_A)
% 1.43/1.68        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68            = (k2_struct_0 @ sk_A))
% 1.43/1.68        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['34', '35'])).
% 1.43/1.68  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('38', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (k2_struct_0 @ sk_A))
% 1.43/1.68        | ~ (v1_tops_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.43/1.68      inference('demod', [status(thm)], ['36', '37'])).
% 1.43/1.68  thf('39', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['24', '25'])).
% 1.43/1.68  thf('40', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['24', '25'])).
% 1.43/1.68  thf('41', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (k2_struct_0 @ sk_A))
% 1.43/1.68        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.43/1.68      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.43/1.68  thf('42', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['29', '41'])).
% 1.43/1.68  thf('43', plain,
% 1.43/1.68      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['32', '33'])).
% 1.43/1.68  thf(dt_k2_pre_topc, axiom,
% 1.43/1.68    (![A:$i,B:$i]:
% 1.43/1.68     ( ( ( l1_pre_topc @ A ) & 
% 1.43/1.68         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.43/1.68       ( m1_subset_1 @
% 1.43/1.68         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.43/1.68  thf('44', plain,
% 1.43/1.68      (![X14 : $i, X15 : $i]:
% 1.43/1.68         (~ (l1_pre_topc @ X14)
% 1.43/1.68          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.43/1.68          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 1.43/1.68             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 1.43/1.68      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 1.43/1.68  thf('45', plain,
% 1.43/1.68      (((m1_subset_1 @ 
% 1.43/1.68         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.43/1.68        | ~ (l1_pre_topc @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['43', '44'])).
% 1.43/1.68  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('47', plain,
% 1.43/1.68      ((m1_subset_1 @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['45', '46'])).
% 1.43/1.68  thf('48', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['24', '25'])).
% 1.43/1.68  thf('49', plain,
% 1.43/1.68      ((m1_subset_1 @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['47', '48'])).
% 1.43/1.68  thf('50', plain,
% 1.43/1.68      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.43/1.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup+', [status(thm)], ['42', '49'])).
% 1.43/1.68  thf('51', plain,
% 1.43/1.68      (![X6 : $i, X7 : $i]:
% 1.43/1.68         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 1.43/1.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.43/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.43/1.68  thf('52', plain,
% 1.43/1.68      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.43/1.68          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['50', '51'])).
% 1.43/1.68  thf('53', plain,
% 1.43/1.68      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.43/1.68           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.43/1.68         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup+', [status(thm)], ['2', '52'])).
% 1.43/1.68  thf(d10_xboole_0, axiom,
% 1.43/1.68    (![A:$i,B:$i]:
% 1.43/1.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.43/1.68  thf('54', plain,
% 1.43/1.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 1.43/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.43/1.68  thf('55', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.43/1.68      inference('simplify', [status(thm)], ['54'])).
% 1.43/1.68  thf(t3_subset, axiom,
% 1.43/1.68    (![A:$i,B:$i]:
% 1.43/1.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.43/1.68  thf('56', plain,
% 1.43/1.68      (![X10 : $i, X12 : $i]:
% 1.43/1.68         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 1.43/1.68      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.68  thf('57', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.43/1.68      inference('sup-', [status(thm)], ['55', '56'])).
% 1.43/1.68  thf('58', plain,
% 1.43/1.68      (![X6 : $i, X7 : $i]:
% 1.43/1.68         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 1.43/1.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.43/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.43/1.68  thf('59', plain,
% 1.43/1.68      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.43/1.68      inference('sup-', [status(thm)], ['57', '58'])).
% 1.43/1.68  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 1.43/1.68      inference('simplify', [status(thm)], ['54'])).
% 1.43/1.68  thf(l32_xboole_1, axiom,
% 1.43/1.68    (![A:$i,B:$i]:
% 1.43/1.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.43/1.68  thf('61', plain,
% 1.43/1.68      (![X3 : $i, X5 : $i]:
% 1.43/1.68         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 1.43/1.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.43/1.68  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.43/1.68      inference('sup-', [status(thm)], ['60', '61'])).
% 1.43/1.68  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 1.43/1.68      inference('sup-', [status(thm)], ['15', '16'])).
% 1.43/1.68  thf('64', plain,
% 1.43/1.68      ((((k1_xboole_0)
% 1.43/1.68          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['53', '59', '62', '63'])).
% 1.43/1.68  thf('65', plain,
% 1.43/1.68      (![X3 : $i, X4 : $i]:
% 1.43/1.68         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.43/1.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.43/1.68  thf('66', plain,
% 1.43/1.68      (((((k1_xboole_0) != (k1_xboole_0))
% 1.43/1.68         | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['64', '65'])).
% 1.43/1.68  thf('67', plain,
% 1.43/1.68      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('simplify', [status(thm)], ['66'])).
% 1.43/1.68  thf('68', plain,
% 1.43/1.68      (![X0 : $i, X2 : $i]:
% 1.43/1.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.43/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.43/1.68  thf('69', plain,
% 1.43/1.68      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 1.43/1.68         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['67', '68'])).
% 1.43/1.68  thf('70', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['29', '41'])).
% 1.43/1.68  thf('71', plain,
% 1.43/1.68      ((m1_subset_1 @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['47', '48'])).
% 1.43/1.68  thf('72', plain,
% 1.43/1.68      (![X10 : $i, X11 : $i]:
% 1.43/1.68         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 1.43/1.68      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.68  thf('73', plain,
% 1.43/1.68      ((r1_tarski @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (u1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['71', '72'])).
% 1.43/1.68  thf('74', plain,
% 1.43/1.68      (((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup+', [status(thm)], ['70', '73'])).
% 1.43/1.68  thf('75', plain,
% 1.43/1.68      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['69', '74'])).
% 1.43/1.68  thf('76', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf(d1_tops_1, axiom,
% 1.43/1.68    (![A:$i]:
% 1.43/1.68     ( ( l1_pre_topc @ A ) =>
% 1.43/1.68       ( ![B:$i]:
% 1.43/1.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.43/1.68           ( ( k1_tops_1 @ A @ B ) =
% 1.43/1.68             ( k3_subset_1 @
% 1.43/1.68               ( u1_struct_0 @ A ) @ 
% 1.43/1.68               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.43/1.68  thf('77', plain,
% 1.43/1.68      (![X17 : $i, X18 : $i]:
% 1.43/1.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.43/1.68          | ((k1_tops_1 @ X18 @ X17)
% 1.43/1.68              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 1.43/1.68                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 1.43/1.68          | ~ (l1_pre_topc @ X18))),
% 1.43/1.68      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.43/1.68  thf('78', plain,
% 1.43/1.68      ((~ (l1_pre_topc @ sk_A)
% 1.43/1.68        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68               (k2_pre_topc @ sk_A @ 
% 1.43/1.68                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['76', '77'])).
% 1.43/1.68  thf('79', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('80', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('demod', [status(thm)], ['11', '18'])).
% 1.43/1.68  thf('81', plain,
% 1.43/1.68      (((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('demod', [status(thm)], ['78', '79', '80'])).
% 1.43/1.68  thf('82', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['24', '25'])).
% 1.43/1.68  thf('83', plain,
% 1.43/1.68      (((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('demod', [status(thm)], ['81', '82'])).
% 1.43/1.68  thf('84', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 1.43/1.68             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup+', [status(thm)], ['75', '83'])).
% 1.43/1.68  thf('85', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['29', '41'])).
% 1.43/1.68  thf('86', plain,
% 1.43/1.68      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.43/1.68      inference('sup-', [status(thm)], ['57', '58'])).
% 1.43/1.68  thf('87', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.43/1.68      inference('sup-', [status(thm)], ['60', '61'])).
% 1.43/1.68  thf('88', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.43/1.68         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 1.43/1.68  thf('89', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 1.43/1.68         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('split', [status(esa)], ['0'])).
% 1.43/1.68  thf('90', plain,
% 1.43/1.68      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.43/1.68         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 1.43/1.68             ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['88', '89'])).
% 1.43/1.68  thf('91', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.43/1.68       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('simplify', [status(thm)], ['90'])).
% 1.43/1.68  thf('92', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.43/1.68       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('split', [status(esa)], ['3'])).
% 1.43/1.68  thf('93', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('split', [status(esa)], ['3'])).
% 1.43/1.68  thf('94', plain,
% 1.43/1.68      ((m1_subset_1 @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['47', '48'])).
% 1.43/1.68  thf('95', plain,
% 1.43/1.68      (![X6 : $i, X7 : $i]:
% 1.43/1.68         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 1.43/1.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 1.43/1.68      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.43/1.68  thf('96', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.43/1.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['94', '95'])).
% 1.43/1.68  thf('97', plain,
% 1.43/1.68      (((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('demod', [status(thm)], ['81', '82'])).
% 1.43/1.68  thf('98', plain,
% 1.43/1.68      (((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('sup+', [status(thm)], ['96', '97'])).
% 1.43/1.68  thf('99', plain,
% 1.43/1.68      (![X3 : $i, X4 : $i]:
% 1.43/1.68         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.43/1.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.43/1.68  thf('100', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 1.43/1.68        | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['98', '99'])).
% 1.43/1.68  thf('101', plain,
% 1.43/1.68      (((((k1_xboole_0) != (k1_xboole_0))
% 1.43/1.68         | (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['93', '100'])).
% 1.43/1.68  thf('102', plain,
% 1.43/1.68      (((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('simplify', [status(thm)], ['101'])).
% 1.43/1.68  thf('103', plain,
% 1.43/1.68      (![X0 : $i, X2 : $i]:
% 1.43/1.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.43/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.43/1.68  thf('104', plain,
% 1.43/1.68      (((~ (r1_tarski @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68            (u1_struct_0 @ sk_A))
% 1.43/1.68         | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68             = (u1_struct_0 @ sk_A))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['102', '103'])).
% 1.43/1.68  thf('105', plain,
% 1.43/1.68      ((r1_tarski @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (u1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['71', '72'])).
% 1.43/1.68  thf('106', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (u1_struct_0 @ sk_A)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('demod', [status(thm)], ['104', '105'])).
% 1.43/1.68  thf('107', plain,
% 1.43/1.68      (((r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('simplify', [status(thm)], ['101'])).
% 1.43/1.68  thf('108', plain,
% 1.43/1.68      ((r1_tarski @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (u1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['71', '72'])).
% 1.43/1.68  thf('109', plain,
% 1.43/1.68      (![X0 : $i, X2 : $i]:
% 1.43/1.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.43/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.43/1.68  thf('110', plain,
% 1.43/1.68      ((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68           (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 1.43/1.68        | ((u1_struct_0 @ sk_A)
% 1.43/1.68            = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['108', '109'])).
% 1.43/1.68  thf('111', plain,
% 1.43/1.68      ((((u1_struct_0 @ sk_A)
% 1.43/1.68          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['107', '110'])).
% 1.43/1.68  thf('112', plain,
% 1.43/1.68      (![X13 : $i]:
% 1.43/1.68         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.43/1.68  thf('113', plain,
% 1.43/1.68      (((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('sup+', [status(thm)], ['96', '97'])).
% 1.43/1.68  thf('114', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 1.43/1.68             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.43/1.68        | ~ (l1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup+', [status(thm)], ['112', '113'])).
% 1.43/1.68  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 1.43/1.68      inference('sup-', [status(thm)], ['15', '16'])).
% 1.43/1.68  thf('116', plain,
% 1.43/1.68      (((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 1.43/1.68            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 1.43/1.68      inference('demod', [status(thm)], ['114', '115'])).
% 1.43/1.68  thf('117', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B)
% 1.43/1.68          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup+', [status(thm)], ['111', '116'])).
% 1.43/1.68  thf('118', plain,
% 1.43/1.68      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('split', [status(esa)], ['3'])).
% 1.43/1.68  thf('119', plain,
% 1.43/1.68      ((((k1_xboole_0)
% 1.43/1.68          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('demod', [status(thm)], ['117', '118'])).
% 1.43/1.68  thf('120', plain,
% 1.43/1.68      (![X3 : $i, X4 : $i]:
% 1.43/1.68         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 1.43/1.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.43/1.68  thf('121', plain,
% 1.43/1.68      (((((k1_xboole_0) != (k1_xboole_0))
% 1.43/1.68         | (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['119', '120'])).
% 1.43/1.68  thf('122', plain,
% 1.43/1.68      (((r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('simplify', [status(thm)], ['121'])).
% 1.43/1.68  thf('123', plain,
% 1.43/1.68      (![X0 : $i, X2 : $i]:
% 1.43/1.68         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.43/1.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.43/1.68  thf('124', plain,
% 1.43/1.68      (((~ (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 1.43/1.68         | ((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['122', '123'])).
% 1.43/1.68  thf('125', plain,
% 1.43/1.68      ((((u1_struct_0 @ sk_A)
% 1.43/1.68          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['107', '110'])).
% 1.43/1.68  thf('126', plain,
% 1.43/1.68      (![X13 : $i]:
% 1.43/1.68         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.43/1.68  thf('127', plain,
% 1.43/1.68      ((r1_tarski @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (u1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['71', '72'])).
% 1.43/1.68  thf('128', plain,
% 1.43/1.68      (((r1_tarski @ 
% 1.43/1.68         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68         (k2_struct_0 @ sk_A))
% 1.43/1.68        | ~ (l1_struct_0 @ sk_A))),
% 1.43/1.68      inference('sup+', [status(thm)], ['126', '127'])).
% 1.43/1.68  thf('129', plain, ((l1_struct_0 @ sk_A)),
% 1.43/1.68      inference('sup-', [status(thm)], ['15', '16'])).
% 1.43/1.68  thf('130', plain,
% 1.43/1.68      ((r1_tarski @ 
% 1.43/1.68        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 1.43/1.68        (k2_struct_0 @ sk_A))),
% 1.43/1.68      inference('demod', [status(thm)], ['128', '129'])).
% 1.43/1.68  thf('131', plain,
% 1.43/1.68      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup+', [status(thm)], ['125', '130'])).
% 1.43/1.68  thf('132', plain,
% 1.43/1.68      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('demod', [status(thm)], ['124', '131'])).
% 1.43/1.68  thf('133', plain,
% 1.43/1.68      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68          = (k2_struct_0 @ sk_A)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('demod', [status(thm)], ['106', '132'])).
% 1.43/1.68  thf('134', plain,
% 1.43/1.68      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['32', '33'])).
% 1.43/1.68  thf('135', plain,
% 1.43/1.68      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('sup-', [status(thm)], ['24', '25'])).
% 1.43/1.68  thf('136', plain,
% 1.43/1.68      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 1.43/1.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['134', '135'])).
% 1.43/1.68  thf('137', plain,
% 1.43/1.68      (![X19 : $i, X20 : $i]:
% 1.43/1.68         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 1.43/1.68          | ((k2_pre_topc @ X20 @ X19) != (k2_struct_0 @ X20))
% 1.43/1.68          | (v1_tops_1 @ X19 @ X20)
% 1.43/1.68          | ~ (l1_pre_topc @ X20))),
% 1.43/1.68      inference('cnf', [status(esa)], [d3_tops_1])).
% 1.43/1.68  thf('138', plain,
% 1.43/1.68      ((~ (l1_pre_topc @ sk_A)
% 1.43/1.68        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.43/1.68        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68            != (k2_struct_0 @ sk_A)))),
% 1.43/1.68      inference('sup-', [status(thm)], ['136', '137'])).
% 1.43/1.68  thf('139', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('140', plain,
% 1.43/1.68      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 1.43/1.68        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 1.43/1.68            != (k2_struct_0 @ sk_A)))),
% 1.43/1.68      inference('demod', [status(thm)], ['138', '139'])).
% 1.43/1.68  thf('141', plain,
% 1.43/1.68      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 1.43/1.68         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['133', '140'])).
% 1.43/1.68  thf('142', plain,
% 1.43/1.68      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('simplify', [status(thm)], ['141'])).
% 1.43/1.68  thf('143', plain,
% 1.43/1.68      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('144', plain,
% 1.43/1.68      (![X21 : $i, X22 : $i]:
% 1.43/1.68         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.43/1.68          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 1.43/1.68          | (v2_tops_1 @ X21 @ X22)
% 1.43/1.68          | ~ (l1_pre_topc @ X22))),
% 1.43/1.68      inference('cnf', [status(esa)], [d4_tops_1])).
% 1.43/1.68  thf('145', plain,
% 1.43/1.68      ((~ (l1_pre_topc @ sk_A)
% 1.43/1.68        | (v2_tops_1 @ sk_B @ sk_A)
% 1.43/1.68        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['143', '144'])).
% 1.43/1.68  thf('146', plain, ((l1_pre_topc @ sk_A)),
% 1.43/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.68  thf('147', plain,
% 1.43/1.68      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.43/1.68         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 1.43/1.68      inference('demod', [status(thm)], ['19', '26'])).
% 1.43/1.68  thf('148', plain,
% 1.43/1.68      (((v2_tops_1 @ sk_B @ sk_A)
% 1.43/1.68        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 1.43/1.68      inference('demod', [status(thm)], ['145', '146', '147'])).
% 1.43/1.68  thf('149', plain,
% 1.43/1.68      (((v2_tops_1 @ sk_B @ sk_A))
% 1.43/1.68         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 1.43/1.68      inference('sup-', [status(thm)], ['142', '148'])).
% 1.43/1.68  thf('150', plain,
% 1.43/1.68      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 1.43/1.68      inference('split', [status(esa)], ['0'])).
% 1.43/1.68  thf('151', plain,
% 1.43/1.68      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 1.43/1.68       ((v2_tops_1 @ sk_B @ sk_A))),
% 1.43/1.68      inference('sup-', [status(thm)], ['149', '150'])).
% 1.43/1.68  thf('152', plain, ($false),
% 1.43/1.68      inference('sat_resolution*', [status(thm)], ['1', '91', '92', '151'])).
% 1.43/1.68  
% 1.43/1.68  % SZS output end Refutation
% 1.43/1.68  
% 1.43/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
