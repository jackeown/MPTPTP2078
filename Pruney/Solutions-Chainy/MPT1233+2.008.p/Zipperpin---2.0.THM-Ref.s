%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j5EXow4uLf

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:50 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 176 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   21
%              Number of atoms          :  614 (1024 expanded)
%              Number of equality atoms :   54 ( 104 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X20 ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
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
    ! [X21: $i] :
      ( ( ( k2_struct_0 @ X21 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X21 ) @ ( k1_struct_0 @ X21 ) ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X9: $i] :
      ( ( k2_subset_1 @ X9 )
      = ( k3_subset_1 @ X9 @ ( k1_subset_1 @ X9 ) ) ) ),
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
    ! [X9: $i] :
      ( X9
      = ( k3_subset_1 @ X9 @ ( k1_subset_1 @ X9 ) ) ) ),
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
    ! [X5: $i] :
      ( ( k1_subset_1 @ X5 )
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k1_subset_1 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( k1_subset_1 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_subset_1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v4_pre_topc @ X17 @ X18 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','34'])).

thf('36',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
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

thf('39',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v4_pre_topc @ X22 @ X23 )
      | ( ( k2_pre_topc @ X23 @ X22 )
        = X22 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k1_subset_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( ( k1_tops_1 @ X25 @ X24 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k2_pre_topc @ X25 @ ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 ) ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_subset_1 @ X8 @ ( k3_subset_1 @ X8 @ X7 ) )
        = X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','68'])).

thf('70',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('72',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(simplify,[status(thm)],['72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j5EXow4uLf
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:54:59 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.48/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.67  % Solved by: fo/fo7.sh
% 0.48/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.67  % done 646 iterations in 0.235s
% 0.48/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.67  % SZS output start Refutation
% 0.48/0.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.48/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.48/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.48/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.48/0.67  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.48/0.67  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.48/0.67  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.48/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.67  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.48/0.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.48/0.67  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.48/0.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.48/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.67  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.48/0.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.48/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.48/0.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.48/0.67  thf(fc3_struct_0, axiom,
% 0.48/0.67    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.48/0.67  thf('0', plain,
% 0.48/0.67      (![X20 : $i]:
% 0.48/0.67         ((v1_xboole_0 @ (k1_struct_0 @ X20)) | ~ (l1_struct_0 @ X20))),
% 0.48/0.67      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.48/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.48/0.67  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.67  thf(t8_boole, axiom,
% 0.48/0.67    (![A:$i,B:$i]:
% 0.48/0.67     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.48/0.67  thf('2', plain,
% 0.48/0.67      (![X3 : $i, X4 : $i]:
% 0.48/0.67         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t8_boole])).
% 0.48/0.67  thf('3', plain,
% 0.48/0.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.67      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.67  thf('4', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.48/0.67      inference('sup-', [status(thm)], ['0', '3'])).
% 0.48/0.67  thf(t27_pre_topc, axiom,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( l1_struct_0 @ A ) =>
% 0.48/0.67       ( ( k2_struct_0 @ A ) =
% 0.48/0.67         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.48/0.67  thf('5', plain,
% 0.48/0.67      (![X21 : $i]:
% 0.48/0.67         (((k2_struct_0 @ X21)
% 0.48/0.67            = (k3_subset_1 @ (u1_struct_0 @ X21) @ (k1_struct_0 @ X21)))
% 0.48/0.67          | ~ (l1_struct_0 @ X21))),
% 0.48/0.67      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.48/0.67  thf('6', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (((k2_struct_0 @ X0)
% 0.48/0.67            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.48/0.67          | ~ (l1_struct_0 @ X0)
% 0.48/0.67          | ~ (l1_struct_0 @ X0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.48/0.67  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.48/0.67  thf('7', plain, (![X5 : $i]: ((k1_subset_1 @ X5) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.48/0.67  thf(t22_subset_1, axiom,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.48/0.67  thf('8', plain,
% 0.48/0.67      (![X9 : $i]:
% 0.48/0.67         ((k2_subset_1 @ X9) = (k3_subset_1 @ X9 @ (k1_subset_1 @ X9)))),
% 0.48/0.67      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.48/0.67  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.48/0.67  thf('9', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.48/0.67      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.48/0.67  thf('10', plain,
% 0.48/0.67      (![X9 : $i]: ((X9) = (k3_subset_1 @ X9 @ (k1_subset_1 @ X9)))),
% 0.48/0.67      inference('demod', [status(thm)], ['8', '9'])).
% 0.48/0.67  thf('11', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.48/0.67      inference('sup+', [status(thm)], ['7', '10'])).
% 0.48/0.67  thf('12', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.48/0.67          | ~ (l1_struct_0 @ X0)
% 0.48/0.67          | ~ (l1_struct_0 @ X0))),
% 0.48/0.67      inference('demod', [status(thm)], ['6', '11'])).
% 0.48/0.67  thf('13', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.48/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.48/0.67  thf(t43_tops_1, conjecture,
% 0.48/0.67    (![A:$i]:
% 0.48/0.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.67       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.48/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.67    (~( ![A:$i]:
% 0.48/0.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.67          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.48/0.67    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.48/0.67  thf('14', plain,
% 0.48/0.67      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.48/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.67  thf('15', plain,
% 0.48/0.67      (![X0 : $i]:
% 0.48/0.67         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.48/0.67      inference('simplify', [status(thm)], ['12'])).
% 0.48/0.67  thf('16', plain, (![X5 : $i]: ((k1_subset_1 @ X5) = (k1_xboole_0))),
% 0.48/0.67      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.48/0.67  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.67  thf('18', plain, (![X0 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['16', '17'])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X3 : $i, X4 : $i]:
% 0.48/0.68         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t8_boole])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k1_subset_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.68  thf('21', plain, (![X5 : $i]: ((k1_subset_1 @ X5) = (k1_xboole_0))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.48/0.68  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (((k1_subset_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['18', '19'])).
% 0.48/0.68  thf('24', plain, (![X5 : $i]: ((k1_subset_1 @ X5) = (k1_xboole_0))),
% 0.48/0.68      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.48/0.68  thf(t4_subset_1, axiom,
% 0.48/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.68  thf(t3_subset, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.48/0.68  thf('26', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i]:
% 0.48/0.68         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('27', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.48/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k1_subset_1 @ X0) @ X1)),
% 0.48/0.68      inference('sup+', [status(thm)], ['24', '27'])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['23', '28'])).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X11 : $i, X13 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.48/0.68  thf(cc2_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.48/0.68          | (v4_pre_topc @ X17 @ X18)
% 0.48/0.68          | ~ (v1_xboole_0 @ X17)
% 0.48/0.68          | ~ (l1_pre_topc @ X18)
% 0.48/0.68          | ~ (v2_pre_topc @ X18))),
% 0.48/0.68      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (v1_xboole_0 @ X1)
% 0.48/0.68          | ~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_xboole_0 @ X1)
% 0.48/0.68          | (v4_pre_topc @ X1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.48/0.68  thf('34', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((v4_pre_topc @ X1 @ X0)
% 0.48/0.68          | ~ (l1_pre_topc @ X0)
% 0.48/0.68          | ~ (v2_pre_topc @ X0)
% 0.48/0.68          | ~ (v1_xboole_0 @ X1))),
% 0.48/0.68      inference('simplify', [status(thm)], ['33'])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (v1_xboole_0 @ X0)
% 0.48/0.68          | ~ (v2_pre_topc @ sk_A)
% 0.48/0.68          | (v4_pre_topc @ X0 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['22', '34'])).
% 0.48/0.68  thf('36', plain, ((v2_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['35', '36'])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.68  thf(t52_pre_topc, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.48/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.48/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (![X22 : $i, X23 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.48/0.68          | ~ (v4_pre_topc @ X22 @ X23)
% 0.48/0.68          | ((k2_pre_topc @ X23 @ X22) = (X22))
% 0.48/0.68          | ~ (l1_pre_topc @ X23))),
% 0.48/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.68          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['38', '39'])).
% 0.48/0.68  thf('41', plain,
% 0.48/0.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.68        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['37', '40'])).
% 0.48/0.68  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.68  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('44', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.48/0.68  thf('45', plain,
% 0.48/0.68      (![X0 : $i]: ((k2_pre_topc @ sk_A @ (k1_subset_1 @ X0)) = (k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['21', '44'])).
% 0.48/0.68  thf('46', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (((k2_pre_topc @ sk_A @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['20', '45'])).
% 0.48/0.68  thf(d10_xboole_0, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.48/0.68  thf('47', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.48/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.48/0.68  thf('48', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.48/0.68      inference('simplify', [status(thm)], ['47'])).
% 0.48/0.68  thf('49', plain,
% 0.48/0.68      (![X11 : $i, X13 : $i]:
% 0.48/0.68         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.48/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.48/0.68  thf('50', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['48', '49'])).
% 0.48/0.68  thf(d1_tops_1, axiom,
% 0.48/0.68    (![A:$i]:
% 0.48/0.68     ( ( l1_pre_topc @ A ) =>
% 0.48/0.68       ( ![B:$i]:
% 0.48/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.48/0.68           ( ( k1_tops_1 @ A @ B ) =
% 0.48/0.68             ( k3_subset_1 @
% 0.48/0.68               ( u1_struct_0 @ A ) @ 
% 0.48/0.68               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.48/0.68  thf('51', plain,
% 0.48/0.68      (![X24 : $i, X25 : $i]:
% 0.48/0.68         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.48/0.68          | ((k1_tops_1 @ X25 @ X24)
% 0.48/0.68              = (k3_subset_1 @ (u1_struct_0 @ X25) @ 
% 0.48/0.68                 (k2_pre_topc @ X25 @ (k3_subset_1 @ (u1_struct_0 @ X25) @ X24))))
% 0.48/0.68          | ~ (l1_pre_topc @ X25))),
% 0.48/0.68      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.48/0.68  thf('52', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.68              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.68                 (k2_pre_topc @ X0 @ 
% 0.48/0.68                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.48/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.48/0.68  thf('53', plain,
% 0.48/0.68      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.48/0.68  thf(involutiveness_k3_subset_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.48/0.68       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.48/0.68  thf('54', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i]:
% 0.48/0.68         (((k3_subset_1 @ X8 @ (k3_subset_1 @ X8 @ X7)) = (X7))
% 0.48/0.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.48/0.68      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.48/0.68  thf('55', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['53', '54'])).
% 0.48/0.68  thf('56', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['7', '10'])).
% 0.48/0.68  thf('57', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.68      inference('demod', [status(thm)], ['55', '56'])).
% 0.48/0.68  thf('58', plain,
% 0.48/0.68      (![X0 : $i]:
% 0.48/0.68         (~ (l1_pre_topc @ X0)
% 0.48/0.68          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.48/0.68              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.48/0.68                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.48/0.68      inference('demod', [status(thm)], ['52', '57'])).
% 0.48/0.68  thf('59', plain,
% 0.48/0.68      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.48/0.68          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.48/0.68        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.48/0.68        | ~ (l1_pre_topc @ sk_A))),
% 0.48/0.68      inference('sup+', [status(thm)], ['46', '58'])).
% 0.48/0.68  thf('60', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['7', '10'])).
% 0.48/0.68  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.48/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.48/0.68  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('63', plain,
% 0.48/0.68      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.48/0.68  thf('64', plain,
% 0.48/0.68      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.48/0.68        | ~ (l1_struct_0 @ sk_A))),
% 0.48/0.68      inference('sup+', [status(thm)], ['15', '63'])).
% 0.48/0.68  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(dt_l1_pre_topc, axiom,
% 0.48/0.68    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.48/0.68  thf('66', plain,
% 0.48/0.68      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_pre_topc @ X19))),
% 0.48/0.68      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.48/0.68  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.48/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.48/0.68  thf('68', plain,
% 0.48/0.68      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['64', '67'])).
% 0.48/0.68  thf('69', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['14', '68'])).
% 0.48/0.68  thf('70', plain,
% 0.48/0.68      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.48/0.68      inference('sup-', [status(thm)], ['13', '69'])).
% 0.48/0.68  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.48/0.68      inference('sup-', [status(thm)], ['65', '66'])).
% 0.48/0.68  thf('72', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.48/0.68      inference('demod', [status(thm)], ['70', '71'])).
% 0.48/0.68  thf('73', plain, ($false), inference('simplify', [status(thm)], ['72'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
