%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sZj4iXBGT5

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:53 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 183 expanded)
%              Number of leaves         :   32 (  69 expanded)
%              Depth                    :   21
%              Number of atoms          :  704 (1108 expanded)
%              Number of equality atoms :   60 ( 105 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
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
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_struct_0 @ X16 ) ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k2_subset_1 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X6: $i] :
      ( X6
      = ( k3_subset_1 @ X6 @ ( k1_subset_1 @ X6 ) ) ) ),
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
    ! [X15: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('16',plain,(
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_subset_1 @ X1 )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_subset_1 @ X1 )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_struct_0 @ X0 )
        = ( k1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_struct_0 @ X16 ) ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_subset_1 @ X1 )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k1_struct_0 @ X1 ) ) )
        = ( k1_struct_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = ( k1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_subset_1 @ X1 )
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('37',plain,(
    ! [X2: $i] :
      ( ( k1_subset_1 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v4_pre_topc @ X11 @ X12 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
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

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v4_pre_topc @ X17 @ X18 )
      | ( ( k2_pre_topc @ X18 @ X17 )
        = X17 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k1_subset_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['58'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( l1_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( ( k1_tops_1 @ X20 @ X19 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ ( k2_pre_topc @ X20 @ ( k3_subset_1 @ ( u1_struct_0 @ X20 ) @ X19 ) ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('63',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['59','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('67',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','69','70'])).

thf('72',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','71'])).

thf('73',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('75',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference(simplify,[status(thm)],['75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sZj4iXBGT5
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.77/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.77/0.93  % Solved by: fo/fo7.sh
% 0.77/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.93  % done 836 iterations in 0.471s
% 0.77/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.77/0.93  % SZS output start Refutation
% 0.77/0.93  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.77/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.93  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.77/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.93  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.77/0.93  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.77/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.77/0.93  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.77/0.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.77/0.93  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.77/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.93  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.77/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.77/0.93  thf(fc3_struct_0, axiom,
% 0.77/0.93    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.77/0.93  thf('0', plain,
% 0.77/0.93      (![X15 : $i]:
% 0.77/0.93         ((v1_xboole_0 @ (k1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.77/0.93      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.77/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.77/0.93  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.93  thf(t8_boole, axiom,
% 0.77/0.93    (![A:$i,B:$i]:
% 0.77/0.93     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.77/0.93  thf('2', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.77/0.93      inference('cnf', [status(esa)], [t8_boole])).
% 0.77/0.93  thf('3', plain,
% 0.77/0.93      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.93  thf('4', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['0', '3'])).
% 0.77/0.93  thf(t27_pre_topc, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( l1_struct_0 @ A ) =>
% 0.77/0.93       ( ( k2_struct_0 @ A ) =
% 0.77/0.93         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.77/0.93  thf('5', plain,
% 0.77/0.93      (![X16 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X16)
% 0.77/0.93            = (k3_subset_1 @ (u1_struct_0 @ X16) @ (k1_struct_0 @ X16)))
% 0.77/0.93          | ~ (l1_struct_0 @ X16))),
% 0.77/0.93      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.77/0.93  thf('6', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X0)
% 0.77/0.93            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['4', '5'])).
% 0.77/0.93  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.77/0.93  thf('7', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.77/0.93  thf(t22_subset_1, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.77/0.93  thf('8', plain,
% 0.77/0.93      (![X6 : $i]:
% 0.77/0.93         ((k2_subset_1 @ X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.77/0.93      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.77/0.93  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.77/0.93  thf('9', plain, (![X3 : $i]: ((k2_subset_1 @ X3) = (X3))),
% 0.77/0.93      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.77/0.93  thf('10', plain,
% 0.77/0.93      (![X6 : $i]: ((X6) = (k3_subset_1 @ X6 @ (k1_subset_1 @ X6)))),
% 0.77/0.93      inference('demod', [status(thm)], ['8', '9'])).
% 0.77/0.93  thf('11', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['7', '10'])).
% 0.77/0.93  thf('12', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X0))),
% 0.77/0.93      inference('demod', [status(thm)], ['6', '11'])).
% 0.77/0.93  thf('13', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.77/0.93      inference('simplify', [status(thm)], ['12'])).
% 0.77/0.93  thf(t43_tops_1, conjecture,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.93       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.77/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.93    (~( ![A:$i]:
% 0.77/0.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.93          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.77/0.93    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.77/0.93  thf('14', plain,
% 0.77/0.93      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('15', plain,
% 0.77/0.93      (![X15 : $i]:
% 0.77/0.93         ((v1_xboole_0 @ (k1_struct_0 @ X15)) | ~ (l1_struct_0 @ X15))),
% 0.77/0.93      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.77/0.93  thf('16', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.77/0.93  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.93  thf('18', plain, (![X0 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['16', '17'])).
% 0.77/0.93  thf('19', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.77/0.93      inference('cnf', [status(esa)], [t8_boole])).
% 0.77/0.93  thf('20', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (((k1_subset_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.77/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.93  thf('21', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0) | ((k1_subset_1 @ X1) = (k1_struct_0 @ X0)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['15', '20'])).
% 0.77/0.93  thf('22', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0) | ((k1_subset_1 @ X1) = (k1_struct_0 @ X0)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['15', '20'])).
% 0.77/0.93  thf('23', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (((k1_struct_0 @ X0) = (k1_struct_0 @ X1))
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X1))),
% 0.77/0.93      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.93  thf('24', plain,
% 0.77/0.93      (![X16 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X16)
% 0.77/0.93            = (k3_subset_1 @ (u1_struct_0 @ X16) @ (k1_struct_0 @ X16)))
% 0.77/0.93          | ~ (l1_struct_0 @ X16))),
% 0.77/0.93      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.77/0.93  thf('25', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (((k2_struct_0 @ X1)
% 0.77/0.93            = (k3_subset_1 @ (u1_struct_0 @ X1) @ (k1_struct_0 @ X0)))
% 0.77/0.93          | ~ (l1_struct_0 @ X1)
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X1))),
% 0.77/0.93      inference('sup+', [status(thm)], ['23', '24'])).
% 0.77/0.93  thf('26', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X1)
% 0.77/0.93          | ((k2_struct_0 @ X1)
% 0.77/0.93              = (k3_subset_1 @ (u1_struct_0 @ X1) @ (k1_struct_0 @ X0))))),
% 0.77/0.93      inference('simplify', [status(thm)], ['25'])).
% 0.77/0.93  thf('27', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0) | ((k1_subset_1 @ X1) = (k1_struct_0 @ X0)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['15', '20'])).
% 0.77/0.93  thf('28', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.77/0.93  thf(t4_subset_1, axiom,
% 0.77/0.93    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.77/0.93  thf('29', plain,
% 0.77/0.93      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.77/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.93  thf('30', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.77/0.93      inference('sup+', [status(thm)], ['28', '29'])).
% 0.77/0.93  thf('31', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         ((m1_subset_1 @ (k1_struct_0 @ X0) @ (k1_zfmisc_1 @ X1))
% 0.77/0.93          | ~ (l1_struct_0 @ X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['27', '30'])).
% 0.77/0.93  thf(involutiveness_k3_subset_1, axiom,
% 0.77/0.93    (![A:$i,B:$i]:
% 0.77/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.93       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.77/0.93  thf('32', plain,
% 0.77/0.93      (![X4 : $i, X5 : $i]:
% 0.77/0.93         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.77/0.93          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.77/0.93      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.77/0.93  thf('33', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X1)
% 0.77/0.93          | ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k1_struct_0 @ X1)))
% 0.77/0.93              = (k1_struct_0 @ X1)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['31', '32'])).
% 0.77/0.93  thf('34', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (((k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.77/0.93            = (k1_struct_0 @ X1))
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X1)
% 0.77/0.93          | ~ (l1_struct_0 @ X1))),
% 0.77/0.93      inference('sup+', [status(thm)], ['26', '33'])).
% 0.77/0.93  thf('35', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X1)
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ((k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.77/0.93              = (k1_struct_0 @ X1)))),
% 0.77/0.93      inference('simplify', [status(thm)], ['34'])).
% 0.77/0.93  thf('36', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0) | ((k1_subset_1 @ X1) = (k1_struct_0 @ X0)))),
% 0.77/0.93      inference('sup-', [status(thm)], ['15', '20'])).
% 0.77/0.93  thf('37', plain, (![X2 : $i]: ((k1_subset_1 @ X2) = (k1_xboole_0))),
% 0.77/0.93      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.77/0.93  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('39', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (((k1_subset_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.77/0.93      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.93  thf('40', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.77/0.93      inference('sup+', [status(thm)], ['28', '29'])).
% 0.77/0.93  thf('41', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['39', '40'])).
% 0.77/0.93  thf(cc2_pre_topc, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.77/0.93  thf('42', plain,
% 0.77/0.93      (![X11 : $i, X12 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.77/0.93          | (v4_pre_topc @ X11 @ X12)
% 0.77/0.93          | ~ (v1_xboole_0 @ X11)
% 0.77/0.93          | ~ (l1_pre_topc @ X12)
% 0.77/0.93          | ~ (v2_pre_topc @ X12))),
% 0.77/0.93      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.77/0.93  thf('43', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (v1_xboole_0 @ X1)
% 0.77/0.93          | ~ (v2_pre_topc @ X0)
% 0.77/0.93          | ~ (l1_pre_topc @ X0)
% 0.77/0.93          | ~ (v1_xboole_0 @ X1)
% 0.77/0.93          | (v4_pre_topc @ X1 @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['41', '42'])).
% 0.77/0.93  thf('44', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         ((v4_pre_topc @ X1 @ X0)
% 0.77/0.93          | ~ (l1_pre_topc @ X0)
% 0.77/0.93          | ~ (v2_pre_topc @ X0)
% 0.77/0.93          | ~ (v1_xboole_0 @ X1))),
% 0.77/0.93      inference('simplify', [status(thm)], ['43'])).
% 0.77/0.93  thf('45', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (v1_xboole_0 @ X0)
% 0.77/0.93          | ~ (v2_pre_topc @ sk_A)
% 0.77/0.93          | (v4_pre_topc @ X0 @ sk_A))),
% 0.77/0.93      inference('sup-', [status(thm)], ['38', '44'])).
% 0.77/0.93  thf('46', plain, ((v2_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('47', plain,
% 0.77/0.93      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.77/0.93      inference('demod', [status(thm)], ['45', '46'])).
% 0.77/0.93  thf('48', plain,
% 0.77/0.93      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.77/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.77/0.93  thf(t52_pre_topc, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( l1_pre_topc @ A ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.77/0.93             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.77/0.93               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.77/0.93  thf('49', plain,
% 0.77/0.93      (![X17 : $i, X18 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.93          | ~ (v4_pre_topc @ X17 @ X18)
% 0.77/0.93          | ((k2_pre_topc @ X18 @ X17) = (X17))
% 0.77/0.93          | ~ (l1_pre_topc @ X18))),
% 0.77/0.93      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.77/0.93  thf('50', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (l1_pre_topc @ X0)
% 0.77/0.93          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.77/0.93          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.77/0.93      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.93  thf('51', plain,
% 0.77/0.93      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.77/0.93        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.77/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.93      inference('sup-', [status(thm)], ['47', '50'])).
% 0.77/0.93  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.77/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.77/0.93  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('54', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.93      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.77/0.93  thf('55', plain,
% 0.77/0.93      (![X0 : $i]: ((k2_pre_topc @ sk_A @ (k1_subset_1 @ X0)) = (k1_xboole_0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['37', '54'])).
% 0.77/0.93  thf('56', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k2_pre_topc @ sk_A @ (k1_struct_0 @ X0)) = (k1_xboole_0))
% 0.77/0.93          | ~ (l1_struct_0 @ X0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['36', '55'])).
% 0.77/0.93  thf('57', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (((k2_pre_topc @ sk_A @ 
% 0.77/0.93            (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 0.77/0.93            = (k1_xboole_0))
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_struct_0 @ X1)
% 0.77/0.93          | ~ (l1_struct_0 @ X1))),
% 0.77/0.93      inference('sup+', [status(thm)], ['35', '56'])).
% 0.77/0.93  thf('58', plain,
% 0.77/0.93      (![X0 : $i, X1 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X1)
% 0.77/0.93          | ~ (l1_struct_0 @ X0)
% 0.77/0.93          | ((k2_pre_topc @ sk_A @ 
% 0.77/0.93              (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 0.77/0.93              = (k1_xboole_0)))),
% 0.77/0.93      inference('simplify', [status(thm)], ['57'])).
% 0.77/0.93  thf('59', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k2_pre_topc @ sk_A @ 
% 0.77/0.93            (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))
% 0.77/0.93            = (k1_xboole_0))
% 0.77/0.93          | ~ (l1_struct_0 @ X0))),
% 0.77/0.93      inference('condensation', [status(thm)], ['58'])).
% 0.77/0.93  thf(dt_k2_struct_0, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( l1_struct_0 @ A ) =>
% 0.77/0.93       ( m1_subset_1 @
% 0.77/0.93         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.77/0.93  thf('60', plain,
% 0.77/0.93      (![X13 : $i]:
% 0.77/0.93         ((m1_subset_1 @ (k2_struct_0 @ X13) @ 
% 0.77/0.93           (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.77/0.93          | ~ (l1_struct_0 @ X13))),
% 0.77/0.93      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.77/0.93  thf(d1_tops_1, axiom,
% 0.77/0.93    (![A:$i]:
% 0.77/0.93     ( ( l1_pre_topc @ A ) =>
% 0.77/0.93       ( ![B:$i]:
% 0.77/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.93           ( ( k1_tops_1 @ A @ B ) =
% 0.77/0.93             ( k3_subset_1 @
% 0.77/0.93               ( u1_struct_0 @ A ) @ 
% 0.77/0.93               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.77/0.93  thf('61', plain,
% 0.77/0.93      (![X19 : $i, X20 : $i]:
% 0.77/0.93         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.77/0.93          | ((k1_tops_1 @ X20 @ X19)
% 0.77/0.93              = (k3_subset_1 @ (u1_struct_0 @ X20) @ 
% 0.77/0.93                 (k2_pre_topc @ X20 @ (k3_subset_1 @ (u1_struct_0 @ X20) @ X19))))
% 0.77/0.93          | ~ (l1_pre_topc @ X20))),
% 0.77/0.93      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.77/0.93  thf('62', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (~ (l1_struct_0 @ X0)
% 0.77/0.93          | ~ (l1_pre_topc @ X0)
% 0.77/0.93          | ((k1_tops_1 @ X0 @ (k2_struct_0 @ X0))
% 0.77/0.93              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.77/0.93                 (k2_pre_topc @ X0 @ 
% 0.77/0.93                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))))))),
% 0.77/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.77/0.93  thf(dt_l1_pre_topc, axiom,
% 0.77/0.93    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.77/0.93  thf('63', plain,
% 0.77/0.93      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.77/0.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.77/0.93  thf('64', plain,
% 0.77/0.93      (![X0 : $i]:
% 0.77/0.93         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0))
% 0.77/0.93            = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.77/0.93               (k2_pre_topc @ X0 @ 
% 0.77/0.93                (k3_subset_1 @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))))
% 0.77/0.93          | ~ (l1_pre_topc @ X0))),
% 0.77/0.93      inference('clc', [status(thm)], ['62', '63'])).
% 0.77/0.93  thf('65', plain,
% 0.77/0.93      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.77/0.93          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.77/0.93        | ~ (l1_struct_0 @ sk_A)
% 0.77/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.93      inference('sup+', [status(thm)], ['59', '64'])).
% 0.77/0.93  thf('66', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.77/0.93      inference('sup+', [status(thm)], ['7', '10'])).
% 0.77/0.93  thf('67', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('68', plain,
% 0.77/0.93      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.77/0.93      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.77/0.93  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.93      inference('sup-', [status(thm)], ['67', '68'])).
% 0.77/0.93  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.93  thf('71', plain,
% 0.77/0.93      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.77/0.93      inference('demod', [status(thm)], ['65', '66', '69', '70'])).
% 0.77/0.93  thf('72', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.77/0.93      inference('demod', [status(thm)], ['14', '71'])).
% 0.77/0.93  thf('73', plain,
% 0.77/0.93      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.77/0.93      inference('sup-', [status(thm)], ['13', '72'])).
% 0.77/0.93  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.93      inference('sup-', [status(thm)], ['67', '68'])).
% 0.77/0.93  thf('75', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.77/0.93      inference('demod', [status(thm)], ['73', '74'])).
% 0.77/0.93  thf('76', plain, ($false), inference('simplify', [status(thm)], ['75'])).
% 0.77/0.93  
% 0.77/0.93  % SZS output end Refutation
% 0.77/0.93  
% 0.77/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
