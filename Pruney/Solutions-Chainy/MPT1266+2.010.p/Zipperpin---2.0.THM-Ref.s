%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLs0b0n3LC

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:13 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  183 (1075 expanded)
%              Number of leaves         :   30 ( 323 expanded)
%              Depth                    :   25
%              Number of atoms          : 1616 (10036 expanded)
%              Number of equality atoms :  121 ( 637 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('3',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tops_1 @ X21 @ X22 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v1_tops_1 @ X19 @ X20 )
      | ( ( k2_pre_topc @ X20 @ X19 )
        = ( k2_struct_0 @ X20 ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_pre_topc @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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

thf('54',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('55',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('56',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('59',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('62',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('65',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('69',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['53','67','68'])).

thf('70',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('71',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( r1_tarski @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_struct_0 @ sk_A )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','74'])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('78',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('80',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('84',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['78','84'])).

thf('86',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
      = ( k2_struct_0 @ sk_A ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('87',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['62','66'])).

thf('89',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k1_tops_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( v2_tops_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('94',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('95',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('96',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('98',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('99',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('100',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_pre_topc @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('101',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('106',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('107',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('108',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
        = ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['97','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('111',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X13: $i] :
      ( ( ( k2_struct_0 @ X13 )
        = ( u1_struct_0 @ X13 ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('113',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('114',plain,
    ( ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('116',plain,
    ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('118',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('120',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['111','120'])).

thf('122',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('123',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('125',plain,
    ( ( k1_xboole_0
      = ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['96','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('128',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k3_subset_1 @ X12 @ ( k3_subset_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('129',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('131',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['126','131'])).

thf('133',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ k1_xboole_0 )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('134',plain,
    ( ( ( k2_struct_0 @ sk_A )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('136',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k2_pre_topc @ X20 @ X19 )
       != ( k2_struct_0 @ X20 ) )
      | ( v1_tops_1 @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('137',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['134','139'])).

thf('141',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 ) @ X22 )
      | ( v2_tops_1 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('147',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( v2_tops_1 @ sk_B @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['141','147'])).

thf('149',plain,
    ( ~ ( v2_tops_1 @ sk_B @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('150',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','92','93','150'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wLs0b0n3LC
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.81  % Solved by: fo/fo7.sh
% 0.59/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.81  % done 1176 iterations in 0.351s
% 0.59/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.81  % SZS output start Refutation
% 0.59/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.81  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.59/0.81  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.59/0.81  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.81  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.81  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.59/0.81  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.59/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.81  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.81  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.81  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.59/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.81  thf(t84_tops_1, conjecture,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( v2_tops_1 @ B @ A ) <=>
% 0.59/0.81             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.59/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.81    (~( ![A:$i]:
% 0.59/0.81        ( ( l1_pre_topc @ A ) =>
% 0.59/0.81          ( ![B:$i]:
% 0.59/0.81            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81              ( ( v2_tops_1 @ B @ A ) <=>
% 0.59/0.81                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.59/0.81    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.59/0.81  thf('0', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 0.59/0.81        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('1', plain,
% 0.59/0.81      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.59/0.81       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('split', [status(esa)], ['0'])).
% 0.59/0.81  thf(d3_struct_0, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.59/0.81  thf('2', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('3', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('4', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)) | (v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('5', plain,
% 0.59/0.81      (((v2_tops_1 @ sk_B @ sk_A)) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('split', [status(esa)], ['4'])).
% 0.59/0.81  thf('6', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(d4_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( v2_tops_1 @ B @ A ) <=>
% 0.59/0.81             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.59/0.81  thf('7', plain,
% 0.59/0.81      (![X21 : $i, X22 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.59/0.81          | ~ (v2_tops_1 @ X21 @ X22)
% 0.59/0.81          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.59/0.81          | ~ (l1_pre_topc @ X22))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.59/0.81  thf('8', plain,
% 0.59/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.59/0.81        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.59/0.81  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('10', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(d5_subset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.81       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.59/0.81  thf('11', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('12', plain,
% 0.59/0.81      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.81  thf('13', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('14', plain,
% 0.59/0.81      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.81  thf('15', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.81      inference('sup+', [status(thm)], ['13', '14'])).
% 0.59/0.81  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(dt_l1_pre_topc, axiom,
% 0.59/0.81    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.81  thf('17', plain,
% 0.59/0.81      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_pre_topc @ X16))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.81  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('19', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['15', '18'])).
% 0.59/0.81  thf('20', plain,
% 0.59/0.81      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['12', '19'])).
% 0.59/0.81  thf('21', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('22', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('23', plain,
% 0.59/0.81      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.59/0.81        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.81      inference('sup+', [status(thm)], ['21', '22'])).
% 0.59/0.81  thf('24', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('25', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['23', '24'])).
% 0.59/0.81  thf('26', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('27', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.81  thf('28', plain,
% 0.59/0.81      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '27'])).
% 0.59/0.81  thf('29', plain,
% 0.59/0.81      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.59/0.81        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['8', '9', '28'])).
% 0.59/0.81  thf('30', plain,
% 0.59/0.81      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['5', '29'])).
% 0.59/0.81  thf('31', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('32', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(dt_k3_subset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.81       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.81  thf('33', plain,
% 0.59/0.81      (![X9 : $i, X10 : $i]:
% 0.59/0.81         ((m1_subset_1 @ (k3_subset_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.59/0.81          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.59/0.81  thf('34', plain,
% 0.59/0.81      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.81  thf('35', plain,
% 0.59/0.81      (((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.81      inference('sup+', [status(thm)], ['31', '34'])).
% 0.59/0.81  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('37', plain,
% 0.59/0.81      ((m1_subset_1 @ (k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['35', '36'])).
% 0.59/0.81  thf('38', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('sup-', [status(thm)], ['25', '26'])).
% 0.59/0.81  thf('39', plain,
% 0.59/0.81      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.81  thf(d3_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( v1_tops_1 @ B @ A ) <=>
% 0.59/0.81             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.59/0.81  thf('40', plain,
% 0.59/0.81      (![X19 : $i, X20 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.59/0.81          | ~ (v1_tops_1 @ X19 @ X20)
% 0.59/0.81          | ((k2_pre_topc @ X20 @ X19) = (k2_struct_0 @ X20))
% 0.59/0.81          | ~ (l1_pre_topc @ X20))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.59/0.81  thf('41', plain,
% 0.59/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81            = (k2_struct_0 @ sk_A))
% 0.59/0.81        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.59/0.81  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('43', plain,
% 0.59/0.81      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81          = (k2_struct_0 @ sk_A))
% 0.59/0.81        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['41', '42'])).
% 0.59/0.81  thf('44', plain,
% 0.59/0.81      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81          = (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['30', '43'])).
% 0.59/0.81  thf('45', plain,
% 0.59/0.81      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.81  thf(dt_k2_pre_topc, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.81       ( m1_subset_1 @
% 0.59/0.81         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.81  thf('46', plain,
% 0.59/0.81      (![X14 : $i, X15 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X14)
% 0.59/0.81          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.59/0.81          | (m1_subset_1 @ (k2_pre_topc @ X14 @ X15) @ 
% 0.59/0.81             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.59/0.81  thf('47', plain,
% 0.59/0.81      (((m1_subset_1 @ 
% 0.59/0.81         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.81  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('49', plain,
% 0.59/0.81      ((m1_subset_1 @ 
% 0.59/0.81        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.81  thf('50', plain,
% 0.59/0.81      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['44', '49'])).
% 0.59/0.81  thf('51', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('52', plain,
% 0.59/0.81      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.59/0.81          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.81  thf('53', plain,
% 0.59/0.81      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.59/0.81           = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.59/0.81         | ~ (l1_struct_0 @ sk_A))) <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['3', '52'])).
% 0.59/0.81  thf('54', plain,
% 0.59/0.81      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81          = (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['30', '43'])).
% 0.59/0.81  thf('55', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('56', plain,
% 0.59/0.81      ((m1_subset_1 @ 
% 0.59/0.81        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.81  thf('57', plain,
% 0.59/0.81      (((m1_subset_1 @ 
% 0.59/0.81         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.59/0.81        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.81      inference('sup+', [status(thm)], ['55', '56'])).
% 0.59/0.81  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('59', plain,
% 0.59/0.81      ((m1_subset_1 @ 
% 0.59/0.81        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.81  thf('60', plain,
% 0.59/0.81      (((m1_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['54', '59'])).
% 0.59/0.81  thf('61', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('62', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.59/0.81          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.81  thf(d10_xboole_0, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.81  thf('63', plain,
% 0.59/0.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.81  thf('64', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.81      inference('simplify', [status(thm)], ['63'])).
% 0.59/0.81  thf(l32_xboole_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.81  thf('65', plain,
% 0.59/0.81      (![X3 : $i, X5 : $i]:
% 0.59/0.81         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.59/0.81      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.81  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.81      inference('sup-', [status(thm)], ['64', '65'])).
% 0.59/0.81  thf('67', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.59/0.81          = (k1_xboole_0)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['62', '66'])).
% 0.59/0.81  thf('68', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('69', plain,
% 0.59/0.81      ((((k1_xboole_0)
% 0.59/0.81          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['53', '67', '68'])).
% 0.59/0.81  thf('70', plain,
% 0.59/0.81      (![X3 : $i, X4 : $i]:
% 0.59/0.81         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.59/0.81      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.59/0.81  thf('71', plain,
% 0.59/0.81      (((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.81         | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.81  thf('72', plain,
% 0.59/0.81      (((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('simplify', [status(thm)], ['71'])).
% 0.59/0.81  thf('73', plain,
% 0.59/0.81      (![X0 : $i, X2 : $i]:
% 0.59/0.81         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.59/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.81  thf('74', plain,
% 0.59/0.81      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))
% 0.59/0.81         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.81  thf('75', plain,
% 0.59/0.81      (((~ (r1_tarski @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.59/0.81         | ~ (l1_struct_0 @ sk_A)
% 0.59/0.81         | ((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['2', '74'])).
% 0.59/0.81  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.59/0.81      inference('simplify', [status(thm)], ['63'])).
% 0.59/0.81  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('78', plain,
% 0.59/0.81      ((((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.59/0.81  thf('79', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(d1_tops_1, axiom,
% 0.59/0.81    (![A:$i]:
% 0.59/0.81     ( ( l1_pre_topc @ A ) =>
% 0.59/0.81       ( ![B:$i]:
% 0.59/0.81         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.81           ( ( k1_tops_1 @ A @ B ) =
% 0.59/0.81             ( k3_subset_1 @
% 0.59/0.81               ( u1_struct_0 @ A ) @ 
% 0.59/0.81               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.59/0.81  thf('80', plain,
% 0.59/0.81      (![X17 : $i, X18 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.59/0.81          | ((k1_tops_1 @ X18 @ X17)
% 0.59/0.81              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.59/0.81                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 0.59/0.81          | ~ (l1_pre_topc @ X18))),
% 0.59/0.81      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.59/0.81  thf('81', plain,
% 0.59/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.59/0.81            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.81               (k2_pre_topc @ sk_A @ 
% 0.59/0.81                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.81  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('83', plain,
% 0.59/0.81      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '27'])).
% 0.59/0.81  thf('84', plain,
% 0.59/0.81      (((k1_tops_1 @ sk_A @ sk_B)
% 0.59/0.81         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.81            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.81      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.59/0.81  thf('85', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.59/0.81          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['78', '84'])).
% 0.59/0.81  thf('86', plain,
% 0.59/0.81      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81          = (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['30', '43'])).
% 0.59/0.81  thf('87', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.59/0.81          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['85', '86'])).
% 0.59/0.81  thf('88', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.59/0.81          = (k1_xboole_0)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['62', '66'])).
% 0.59/0.81  thf('89', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.59/0.81         <= (((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup+', [status(thm)], ['87', '88'])).
% 0.59/0.81  thf('90', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.59/0.81         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['0'])).
% 0.59/0.81  thf('91', plain,
% 0.59/0.81      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.81         <= (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.59/0.81             ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['89', '90'])).
% 0.59/0.81  thf('92', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.59/0.81       ~ ((v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('simplify', [status(thm)], ['91'])).
% 0.59/0.81  thf('93', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.59/0.81       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('split', [status(esa)], ['4'])).
% 0.59/0.81  thf('94', plain,
% 0.59/0.81      ((m1_subset_1 @ 
% 0.59/0.81        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.81  thf('95', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('96', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.81  thf('97', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('98', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['4'])).
% 0.59/0.81  thf('99', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf(dt_k1_tops_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( ( l1_pre_topc @ A ) & 
% 0.59/0.81         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.59/0.81       ( m1_subset_1 @
% 0.59/0.81         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.81  thf('100', plain,
% 0.59/0.81      (![X23 : $i, X24 : $i]:
% 0.59/0.81         (~ (l1_pre_topc @ X23)
% 0.59/0.81          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.59/0.81          | (m1_subset_1 @ (k1_tops_1 @ X23 @ X24) @ 
% 0.59/0.81             (k1_zfmisc_1 @ (u1_struct_0 @ X23))))),
% 0.59/0.81      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.59/0.81  thf('101', plain,
% 0.59/0.81      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.81         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.81        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['99', '100'])).
% 0.59/0.81  thf('102', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('103', plain,
% 0.59/0.81      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['101', '102'])).
% 0.59/0.81  thf('104', plain,
% 0.59/0.81      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['98', '103'])).
% 0.59/0.81  thf('105', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('106', plain,
% 0.59/0.81      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['104', '105'])).
% 0.59/0.81  thf(t3_boole, axiom,
% 0.59/0.81    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.81  thf('107', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.81  thf('108', plain,
% 0.59/0.81      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (u1_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['106', '107'])).
% 0.59/0.81  thf('109', plain,
% 0.59/0.81      (((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81           = (u1_struct_0 @ sk_A))
% 0.59/0.81         | ~ (l1_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['97', '108'])).
% 0.59/0.81  thf('110', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('111', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (u1_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['109', '110'])).
% 0.59/0.81  thf('112', plain,
% 0.59/0.81      (![X13 : $i]:
% 0.59/0.81         (((k2_struct_0 @ X13) = (u1_struct_0 @ X13)) | ~ (l1_struct_0 @ X13))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.81  thf('113', plain,
% 0.59/0.81      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['98', '103'])).
% 0.59/0.81  thf('114', plain,
% 0.59/0.81      ((((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))
% 0.59/0.81         | ~ (l1_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['112', '113'])).
% 0.59/0.81  thf('115', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.81  thf('116', plain,
% 0.59/0.81      (((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_A))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['114', '115'])).
% 0.59/0.81  thf('117', plain,
% 0.59/0.81      (![X7 : $i, X8 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.59/0.81          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.59/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.81  thf('118', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['116', '117'])).
% 0.59/0.81  thf('119', plain, (![X6 : $i]: ((k4_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.59/0.81      inference('cnf', [status(esa)], [t3_boole])).
% 0.59/0.81  thf('120', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['118', '119'])).
% 0.59/0.81  thf('121', plain,
% 0.59/0.81      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['111', '120'])).
% 0.59/0.81  thf('122', plain,
% 0.59/0.81      (((k1_tops_1 @ sk_A @ sk_B)
% 0.59/0.81         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.81            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.81      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.59/0.81  thf('123', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B)
% 0.59/0.81          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['121', '122'])).
% 0.59/0.81  thf('124', plain,
% 0.59/0.81      ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('split', [status(esa)], ['4'])).
% 0.59/0.81  thf('125', plain,
% 0.59/0.81      ((((k1_xboole_0)
% 0.59/0.81          = (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['123', '124'])).
% 0.59/0.81  thf('126', plain,
% 0.59/0.81      ((((k1_xboole_0)
% 0.59/0.81          = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81             (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['96', '125'])).
% 0.59/0.81  thf('127', plain,
% 0.59/0.81      ((m1_subset_1 @ 
% 0.59/0.81        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.81  thf(involutiveness_k3_subset_1, axiom,
% 0.59/0.81    (![A:$i,B:$i]:
% 0.59/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.81       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.59/0.81  thf('128', plain,
% 0.59/0.81      (![X11 : $i, X12 : $i]:
% 0.59/0.81         (((k3_subset_1 @ X12 @ (k3_subset_1 @ X12 @ X11)) = (X11))
% 0.59/0.81          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.59/0.81      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.59/0.81  thf('129', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81         (k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.81         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['127', '128'])).
% 0.59/0.81  thf('130', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['94', '95'])).
% 0.59/0.81  thf('131', plain,
% 0.59/0.81      (((k3_subset_1 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81         (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.81          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.81         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B)))),
% 0.59/0.81      inference('demod', [status(thm)], ['129', '130'])).
% 0.59/0.81  thf('132', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup+', [status(thm)], ['126', '131'])).
% 0.59/0.81  thf('133', plain,
% 0.59/0.81      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ k1_xboole_0)
% 0.59/0.81          = (k2_struct_0 @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['118', '119'])).
% 0.59/0.81  thf('134', plain,
% 0.59/0.81      ((((k2_struct_0 @ sk_A)
% 0.59/0.81          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('demod', [status(thm)], ['132', '133'])).
% 0.59/0.81  thf('135', plain,
% 0.59/0.81      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.81        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['37', '38'])).
% 0.59/0.81  thf('136', plain,
% 0.59/0.81      (![X19 : $i, X20 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.59/0.81          | ((k2_pre_topc @ X20 @ X19) != (k2_struct_0 @ X20))
% 0.59/0.81          | (v1_tops_1 @ X19 @ X20)
% 0.59/0.81          | ~ (l1_pre_topc @ X20))),
% 0.59/0.81      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.59/0.81  thf('137', plain,
% 0.59/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.59/0.81        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81            != (k2_struct_0 @ sk_A)))),
% 0.59/0.81      inference('sup-', [status(thm)], ['135', '136'])).
% 0.59/0.81  thf('138', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('139', plain,
% 0.59/0.81      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 0.59/0.81        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))
% 0.59/0.81            != (k2_struct_0 @ sk_A)))),
% 0.59/0.81      inference('demod', [status(thm)], ['137', '138'])).
% 0.59/0.81  thf('140', plain,
% 0.59/0.81      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.59/0.81         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A)))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['134', '139'])).
% 0.59/0.81  thf('141', plain,
% 0.59/0.81      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('simplify', [status(thm)], ['140'])).
% 0.59/0.81  thf('142', plain,
% 0.59/0.81      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('143', plain,
% 0.59/0.81      (![X21 : $i, X22 : $i]:
% 0.59/0.81         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.59/0.81          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X22) @ X21) @ X22)
% 0.59/0.81          | (v2_tops_1 @ X21 @ X22)
% 0.59/0.81          | ~ (l1_pre_topc @ X22))),
% 0.59/0.81      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.59/0.81  thf('144', plain,
% 0.59/0.81      ((~ (l1_pre_topc @ sk_A)
% 0.59/0.81        | (v2_tops_1 @ sk_B @ sk_A)
% 0.59/0.81        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['142', '143'])).
% 0.59/0.81  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.81  thf('146', plain,
% 0.59/0.81      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 0.59/0.81         = (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B))),
% 0.59/0.81      inference('demod', [status(thm)], ['20', '27'])).
% 0.59/0.81  thf('147', plain,
% 0.59/0.81      (((v2_tops_1 @ sk_B @ sk_A)
% 0.59/0.81        | ~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B) @ sk_A))),
% 0.59/0.81      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.59/0.81  thf('148', plain,
% 0.59/0.81      (((v2_tops_1 @ sk_B @ sk_A))
% 0.59/0.81         <= ((((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.59/0.81      inference('sup-', [status(thm)], ['141', '147'])).
% 0.59/0.81  thf('149', plain,
% 0.59/0.81      ((~ (v2_tops_1 @ sk_B @ sk_A)) <= (~ ((v2_tops_1 @ sk_B @ sk_A)))),
% 0.59/0.81      inference('split', [status(esa)], ['0'])).
% 0.59/0.81  thf('150', plain,
% 0.59/0.81      (~ (((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0))) | 
% 0.59/0.81       ((v2_tops_1 @ sk_B @ sk_A))),
% 0.59/0.81      inference('sup-', [status(thm)], ['148', '149'])).
% 0.59/0.81  thf('151', plain, ($false),
% 0.59/0.81      inference('sat_resolution*', [status(thm)], ['1', '92', '93', '150'])).
% 0.59/0.81  
% 0.59/0.81  % SZS output end Refutation
% 0.59/0.81  
% 0.68/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
