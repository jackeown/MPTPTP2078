%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xm68UyN4Nk

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:53 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 165 expanded)
%              Number of leaves         :   36 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  571 ( 955 expanded)
%              Number of equality atoms :   49 (  93 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_struct_0 @ X22 ) ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X5: $i] :
      ( ( k1_subset_1 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = ( k3_subset_1 @ X10 @ ( k1_subset_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X10: $i] :
      ( X10
      = ( k3_subset_1 @ X10 @ ( k1_subset_1 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

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

thf('14',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf('26',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','34'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf('37',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('38',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X7 @ X8 )
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['40','43','48'])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['35','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','59'])).

thf('61',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','60'])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('63',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xm68UyN4Nk
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 1445 iterations in 0.424s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.70/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.70/0.89  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.70/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.70/0.89  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.70/0.89  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.70/0.89  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.70/0.89  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.89  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.70/0.89  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.70/0.89  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.70/0.89  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.70/0.89  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.89  thf(fc3_struct_0, axiom,
% 0.70/0.89    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      (![X21 : $i]:
% 0.70/0.89         ((v1_xboole_0 @ (k1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.70/0.89      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.70/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.70/0.89  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf(t8_boole, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X3 : $i, X4 : $i]:
% 0.70/0.89         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t8_boole])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['0', '3'])).
% 0.70/0.89  thf(t27_pre_topc, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_struct_0 @ A ) =>
% 0.70/0.89       ( ( k2_struct_0 @ A ) =
% 0.70/0.89         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X22 : $i]:
% 0.70/0.89         (((k2_struct_0 @ X22)
% 0.70/0.89            = (k3_subset_1 @ (u1_struct_0 @ X22) @ (k1_struct_0 @ X22)))
% 0.70/0.89          | ~ (l1_struct_0 @ X22))),
% 0.70/0.89      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k2_struct_0 @ X0)
% 0.70/0.89            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.70/0.89          | ~ (l1_struct_0 @ X0)
% 0.70/0.89          | ~ (l1_struct_0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.70/0.89  thf('7', plain, (![X5 : $i]: ((k1_subset_1 @ X5) = (k1_xboole_0))),
% 0.70/0.89      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.70/0.89  thf(t22_subset_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X10 : $i]:
% 0.70/0.89         ((k2_subset_1 @ X10) = (k3_subset_1 @ X10 @ (k1_subset_1 @ X10)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.70/0.89  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.70/0.89  thf('9', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X10 : $i]: ((X10) = (k3_subset_1 @ X10 @ (k1_subset_1 @ X10)))),
% 0.70/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.70/0.89  thf('11', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['7', '10'])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.70/0.89          | ~ (l1_struct_0 @ X0)
% 0.70/0.89          | ~ (l1_struct_0 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['6', '11'])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['12'])).
% 0.70/0.89  thf(t43_tops_1, conjecture,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.89       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i]:
% 0.70/0.89        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.89          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.70/0.89      inference('simplify', [status(thm)], ['12'])).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf(t4_subset_1, axiom,
% 0.70/0.89    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.89  thf(cc2_pre_topc, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X18 : $i, X19 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.70/0.89          | (v4_pre_topc @ X18 @ X19)
% 0.70/0.89          | ~ (v1_xboole_0 @ X18)
% 0.70/0.89          | ~ (l1_pre_topc @ X19)
% 0.70/0.89          | ~ (v2_pre_topc @ X19))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v2_pre_topc @ X0)
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.89          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.70/0.89  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v2_pre_topc @ X0)
% 0.70/0.89          | ~ (l1_pre_topc @ X0)
% 0.70/0.89          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v4_pre_topc @ X0 @ X1)
% 0.70/0.89          | ~ (v1_xboole_0 @ X0)
% 0.70/0.89          | ~ (l1_pre_topc @ X1)
% 0.70/0.89          | ~ (v2_pre_topc @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['18', '23'])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v2_pre_topc @ sk_A)
% 0.70/0.89          | ~ (v1_xboole_0 @ X0)
% 0.70/0.89          | (v4_pre_topc @ X0 @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['17', '24'])).
% 0.70/0.89  thf('26', plain, ((v2_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['25', '26'])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.70/0.89      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.70/0.89  thf(t52_pre_topc, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_pre_topc @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.70/0.89             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.70/0.89               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X23 : $i, X24 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.70/0.89          | ~ (v4_pre_topc @ X23 @ X24)
% 0.70/0.89          | ((k2_pre_topc @ X24 @ X23) = (X23))
% 0.70/0.89          | ~ (l1_pre_topc @ X24))),
% 0.70/0.89      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ X0)
% 0.70/0.89          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.70/0.89          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['28', '29'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.89        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.70/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['27', '30'])).
% 0.70/0.89  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('34', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.89      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.70/0.89  thf('35', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k2_pre_topc @ sk_A @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['16', '34'])).
% 0.70/0.89  thf(dt_k2_subset_1, axiom,
% 0.70/0.89    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.70/0.89  thf('37', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.70/0.89      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.70/0.89  thf('38', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.70/0.89      inference('demod', [status(thm)], ['36', '37'])).
% 0.70/0.89  thf(d1_tops_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( l1_pre_topc @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.70/0.89           ( ( k1_tops_1 @ A @ B ) =
% 0.70/0.89             ( k3_subset_1 @
% 0.70/0.89               ( u1_struct_0 @ A ) @ 
% 0.70/0.89               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.70/0.89  thf('39', plain,
% 0.70/0.89      (![X25 : $i, X26 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.70/0.89          | ((k1_tops_1 @ X26 @ X25)
% 0.70/0.89              = (k3_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.70/0.89                 (k2_pre_topc @ X26 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25))))
% 0.70/0.89          | ~ (l1_pre_topc @ X26))),
% 0.70/0.89      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ X0)
% 0.70/0.89          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.70/0.89              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.89                 (k2_pre_topc @ X0 @ 
% 0.70/0.89                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.70/0.89  thf('41', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.70/0.89      inference('demod', [status(thm)], ['36', '37'])).
% 0.70/0.89  thf(d5_subset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.89       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         (((k3_subset_1 @ X7 @ X8) = (k4_xboole_0 @ X7 @ X8))
% 0.70/0.89          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.70/0.89  thf('43', plain,
% 0.70/0.89      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['41', '42'])).
% 0.70/0.89  thf('44', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.70/0.89      inference('demod', [status(thm)], ['36', '37'])).
% 0.70/0.89  thf(t3_subset, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('45', plain,
% 0.70/0.89      (![X12 : $i, X13 : $i]:
% 0.70/0.89         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.89  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.70/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.70/0.89  thf(l32_xboole_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X0 : $i, X2 : $i]:
% 0.70/0.89         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.70/0.89  thf('48', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (l1_pre_topc @ X0)
% 0.70/0.89          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.70/0.89              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.70/0.89                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.70/0.89      inference('demod', [status(thm)], ['40', '43', '48'])).
% 0.70/0.89  thf('50', plain,
% 0.70/0.89      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.70/0.89          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.70/0.89        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.89        | ~ (l1_pre_topc @ sk_A))),
% 0.70/0.89      inference('sup+', [status(thm)], ['35', '49'])).
% 0.70/0.89  thf('51', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.70/0.89      inference('sup+', [status(thm)], ['7', '10'])).
% 0.70/0.89  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.70/0.89  thf('55', plain,
% 0.70/0.89      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.70/0.89        | ~ (l1_struct_0 @ sk_A))),
% 0.70/0.89      inference('sup+', [status(thm)], ['15', '54'])).
% 0.70/0.89  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(dt_l1_pre_topc, axiom,
% 0.70/0.89    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.70/0.89  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['55', '58'])).
% 0.70/0.89  thf('60', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['14', '59'])).
% 0.70/0.89  thf('61', plain,
% 0.70/0.89      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['13', '60'])).
% 0.70/0.89  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 0.70/0.89      inference('sup-', [status(thm)], ['56', '57'])).
% 0.70/0.89  thf('63', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.70/0.89      inference('demod', [status(thm)], ['61', '62'])).
% 0.70/0.89  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
