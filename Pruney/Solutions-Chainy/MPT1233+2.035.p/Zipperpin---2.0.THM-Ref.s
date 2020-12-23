%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u3Y6fQ18AY

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 169 expanded)
%              Number of leaves         :   31 (  66 expanded)
%              Depth                    :   16
%              Number of atoms          :  636 (1090 expanded)
%              Number of equality atoms :   57 ( 117 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t18_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) )
            = ( k2_struct_0 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) )
        = ( k2_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t18_pre_topc])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X5: $i] :
      ( X5
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k4_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t25_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_subset_1 @ X6 @ X7 @ ( k3_subset_1 @ X6 @ X7 ) )
        = ( k2_subset_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t25_subset_1])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k4_subset_1 @ X6 @ X7 @ ( k3_subset_1 @ X6 @ X7 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ X0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','15'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('20',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ ( k1_subset_1 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('27',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

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

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k1_subset_1 @ X1 ) )
      | ~ ( v4_pre_topc @ ( k1_subset_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k1_subset_1 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k1_subset_1 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_pre_topc @ X1 @ k1_xboole_0 )
        = ( k1_subset_1 @ X0 ) )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k1_subset_1 @ X0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i] :
      ( X5
      = ( k3_subset_1 @ X5 @ ( k1_subset_1 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X2
        = ( k3_subset_1 @ X2 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','38'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('41',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('42',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ X19 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_subset_1 @ X4 @ ( k3_subset_1 @ X4 @ X3 ) )
        = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','52'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('54',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','60'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['16','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('64',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u3Y6fQ18AY
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 152 iterations in 0.060s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.51  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.51  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.21/0.51  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.51  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.21/0.51  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.21/0.51  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.51  thf(t4_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf(t18_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_struct_0 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( k4_subset_1 @
% 0.21/0.51               ( u1_struct_0 @ A ) @ B @ 
% 0.21/0.51               ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.21/0.51             ( k2_struct_0 @ A ) ) ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X15 : $i, X16 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.21/0.51          | ((k4_subset_1 @ (u1_struct_0 @ X16) @ X15 @ 
% 0.21/0.51              (k3_subset_1 @ (u1_struct_0 @ X16) @ X15)) = (k2_struct_0 @ X16))
% 0.21/0.51          | ~ (l1_struct_0 @ X16))),
% 0.21/0.51      inference('cnf', [status(esa)], [t18_pre_topc])).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.21/0.51              (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.21/0.51              = (k2_struct_0 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('3', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf(t22_subset_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X5 : $i]:
% 0.21/0.51         ((k2_subset_1 @ X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.21/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.51  thf('5', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X5 : $i]: ((X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('7', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0)
% 0.21/0.51          | ((k4_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ 
% 0.21/0.51              (u1_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['2', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf(t25_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.51         ( k2_subset_1 @ A ) ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (((k4_subset_1 @ X6 @ X7 @ (k3_subset_1 @ X6 @ X7))
% 0.21/0.51            = (k2_subset_1 @ X6))
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t25_subset_1])).
% 0.21/0.51  thf('11', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]:
% 0.21/0.51         (((k4_subset_1 @ X6 @ X7 @ (k3_subset_1 @ X6 @ X7)) = (X6))
% 0.21/0.51          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k4_subset_1 @ X0 @ k1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.21/0.51           = (X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.51  thf('14', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X0 : $i]: ((k4_subset_1 @ X0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_struct_0 @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '15'])).
% 0.21/0.51  thf('18', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf('19', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf(cc2_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.21/0.51          | (v4_pre_topc @ X12 @ X13)
% 0.21/0.51          | ~ (v1_xboole_0 @ X12)
% 0.21/0.51          | ~ (l1_pre_topc @ X13)
% 0.21/0.51          | ~ (v2_pre_topc @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.21/0.51      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((v4_pre_topc @ (k1_subset_1 @ X0) @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X1)
% 0.21/0.51          | ~ (v2_pre_topc @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '24'])).
% 0.21/0.51  thf('26', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf(t52_pre_topc, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.21/0.51             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.21/0.51               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.21/0.51          | ~ (v4_pre_topc @ X17 @ X18)
% 0.21/0.51          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.21/0.51          | ~ (l1_pre_topc @ X18))),
% 0.21/0.51      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ((k2_pre_topc @ X0 @ (k1_subset_1 @ X1)) = (k1_subset_1 @ X1))
% 0.21/0.51          | ~ (v4_pre_topc @ (k1_subset_1 @ X1) @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ((k2_pre_topc @ X0 @ (k1_subset_1 @ X1)) = (k1_subset_1 @ X1))
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_pre_topc @ X0 @ (k1_subset_1 @ X1)) = (k1_subset_1 @ X1))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (((k2_pre_topc @ X1 @ k1_xboole_0) = (k1_subset_1 @ X0))
% 0.21/0.51          | ~ (v2_pre_topc @ X1)
% 0.21/0.51          | ~ (l1_pre_topc @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['18', '32'])).
% 0.21/0.51  thf('34', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf('35', plain, (![X0 : $i]: ((k1_subset_1 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['34', '35'])).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X5 : $i]: ((X5) = (k3_subset_1 @ X5 @ (k1_subset_1 @ X5)))),
% 0.21/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X0 : $i, X2 : $i]:
% 0.21/0.51         (((X2) = (k3_subset_1 @ X2 @ (k2_pre_topc @ X0 @ k1_xboole_0)))
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['33', '38'])).
% 0.21/0.51  thf(dt_k2_subset_1, axiom,
% 0.21/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.21/0.51  thf('41', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.51  thf('42', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 0.21/0.51      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.51  thf(d1_tops_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( l1_pre_topc @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.51           ( ( k1_tops_1 @ A @ B ) =
% 0.21/0.51             ( k3_subset_1 @
% 0.21/0.51               ( u1_struct_0 @ A ) @ 
% 0.21/0.51               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.21/0.51          | ((k1_tops_1 @ X20 @ X19)
% 0.21/0.51              = (k3_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.21/0.51                 (k2_pre_topc @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19))))
% 0.21/0.51          | ~ (l1_pre_topc @ X20))),
% 0.21/0.51      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.21/0.51              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.51                 (k2_pre_topc @ X0 @ 
% 0.21/0.51                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.51  thf(involutiveness_k3_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k3_subset_1 @ X4 @ (k3_subset_1 @ X4 @ X3)) = (X3))
% 0.21/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.21/0.51      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.51  thf('48', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.51  thf('49', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.21/0.51              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.21/0.51                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['44', '49'])).
% 0.21/0.51  thf('51', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['39', '50'])).
% 0.21/0.51  thf('52', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (l1_pre_topc @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.51  thf('53', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.21/0.51          | ~ (l1_struct_0 @ X0)
% 0.21/0.51          | ~ (v2_pre_topc @ X0)
% 0.21/0.51          | ~ (l1_pre_topc @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '52'])).
% 0.21/0.51  thf(t43_tops_1, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.51          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.21/0.51  thf('54', plain,
% 0.21/0.51      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('55', plain,
% 0.21/0.51      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.21/0.51        | ~ (l1_pre_topc @ sk_A)
% 0.21/0.51        | ~ (v2_pre_topc @ sk_A)
% 0.21/0.51        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.51  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(dt_l1_pre_topc, axiom,
% 0.21/0.51    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.51  thf('59', plain,
% 0.21/0.51      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.21/0.51  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('61', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['55', '56', '57', '60'])).
% 0.21/0.51  thf('62', plain,
% 0.21/0.51      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['16', '61'])).
% 0.21/0.51  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.51  thf('64', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['62', '63'])).
% 0.21/0.51  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
