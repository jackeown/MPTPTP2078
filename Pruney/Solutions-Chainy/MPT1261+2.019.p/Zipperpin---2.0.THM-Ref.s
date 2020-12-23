%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GuHwOcTiE3

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:39 EST 2020

% Result     : Theorem 8.93s
% Output     : Refutation 8.93s
% Verified   : 
% Statistics : Number of formulae       :  318 (1742 expanded)
%              Number of leaves         :   52 ( 610 expanded)
%              Depth                    :   29
%              Number of atoms          : 2575 (14602 expanded)
%              Number of equality atoms :  213 (1289 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t77_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( ( k2_tops_1 @ A @ B )
              = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
            <=> ( ( k2_tops_1 @ A @ B )
                = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
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
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['2','7'])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('20',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    r1_tarski @ ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X10 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('27',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('32',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ X17 @ ( k3_tarski @ ( k2_tarski @ X18 @ X19 ) ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X17 @ X18 ) @ X19 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ k1_xboole_0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('40',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k6_subset_1 @ X13 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X12: $i,X13: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k6_subset_1 @ X13 @ X12 ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k6_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['24','44'])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ ( k4_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('47',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('48',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('50',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,
    ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) )
    = sk_B ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('53',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('62',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('63',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('68',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( l1_pre_topc @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( m1_subset_1 @ ( k2_tops_1 @ X54 @ X55 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_tops_1])).

thf('69',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X33: $i,X34: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X33 @ X34 ) @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('73',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('74',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('75',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k3_tarski @ ( k2_tarski @ X37 @ X39 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
        = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
    = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('80',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ( ( k2_pre_topc @ X61 @ X60 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X61 ) @ X60 @ ( k2_tops_1 @ X61 @ X60 ) ) )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['84'])).

thf('86',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('87',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X53 ) ) )
      | ~ ( v4_pre_topc @ X52 @ X53 )
      | ( ( k2_pre_topc @ X53 @ X52 )
        = X52 )
      | ~ ( l1_pre_topc @ X53 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('88',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','90'])).

thf('92',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('94',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('96',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k4_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('97',plain,(
    ! [X40: $i,X41: $i] :
      ( ( k6_subset_1 @ X40 @ X41 )
      = ( k4_xboole_0 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('98',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k7_subset_1 @ X43 @ X42 @ X44 )
        = ( k6_subset_1 @ X42 @ X44 ) ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('101',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('104',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_subset_1 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('106',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k3_tarski @ ( k2_tarski @ X37 @ X39 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('112',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_xboole_0 @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) )
      = ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('113',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('114',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('115',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X26 @ X27 ) )
      = ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('116',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X22 @ ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) )
      = ( k3_tarski @ ( k2_tarski @ X22 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ X0 ) )
      = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['111','116'])).

thf('118',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) )
      = ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k6_subset_1 @ sk_B @ X0 ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['110','121'])).

thf('123',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['101','122'])).

thf('124',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['94','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('126',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X56 @ X57 ) @ X56 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('127',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['124','130'])).

thf('132',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['92'])).

thf('133',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['84'])).

thf('135',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['93','133','134'])).

thf('136',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(simpl_trail,[status(thm)],['91','135'])).

thf('137',plain,
    ( sk_B
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','136'])).

thf('138',plain,
    ( ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k5_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['12','65'])).

thf('139',plain,
    ( sk_B
    = ( k3_tarski @ ( k2_tarski @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['78','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( k6_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['139','144'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('147',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['145','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('151',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k1_tops_1 @ X63 @ X62 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X63 ) @ X62 @ ( k2_tops_1 @ X63 @ X62 ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('152',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('155',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('157',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('158',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k6_subset_1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( k3_tarski @ ( k2_tarski @ X0 @ k1_xboole_0 ) ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('165',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ ( k6_subset_1 @ X1 @ X0 ) @ X1 ) ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['156','170'])).

thf('172',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('180',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['178','181'])).

thf('183',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('184',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X14 @ X15 ) @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k3_tarski @ ( k2_tarski @ X15 @ X16 ) ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('185',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['25','33'])).

thf('187',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('188',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('192',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k6_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['190','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('196',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['195','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('201',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('205',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['194','206'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('208',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('209',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('210',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['210'])).

thf('212',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('213',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k6_subset_1 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('215',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['207','215'])).

thf('217',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['207','215'])).

thf('224',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('226',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ ( k3_tarski @ ( k2_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['185','226'])).

thf('228',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('229',plain,(
    ! [X6: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X6 @ k1_xboole_0 ) )
      = X6 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['228','229'])).

thf('231',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k6_subset_1 @ ( k3_xboole_0 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['227','230'])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('233',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['231','232'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('235',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['233','234'])).

thf('236',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('237',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['235','236'])).

thf('238',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('239',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k6_subset_1 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['237','238'])).

thf('240',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k6_subset_1 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['182','239'])).

thf('241',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['171','240'])).

thf('242',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['155','241'])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('244',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['149','242','243'])).

thf('245',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['92'])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k6_subset_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('247',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k6_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('248',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X10 @ X11 ) @ X10 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('249',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup+',[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('251',plain,(
    r1_tarski @ ( k6_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('253',plain,
    ( ( k6_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_tarski @ ( k2_tarski @ ( k6_subset_1 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) )
      = X20 ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('255',plain,
    ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['253','254'])).

thf('256',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('258',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['255','256','257'])).

thf('259',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('260',plain,
    ( ( k6_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['258','259'])).

thf('261',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['245','246','260'])).

thf('262',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['93','133'])).

thf('263',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['261','262'])).

thf('264',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['244','263'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GuHwOcTiE3
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:19:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.93/9.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.93/9.14  % Solved by: fo/fo7.sh
% 8.93/9.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.93/9.14  % done 19273 iterations in 8.679s
% 8.93/9.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.93/9.14  % SZS output start Refutation
% 8.93/9.14  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.93/9.14  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.93/9.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.93/9.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.93/9.14  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 8.93/9.14  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.93/9.14  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 8.93/9.14  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 8.93/9.14  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.93/9.14  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.93/9.14  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 8.93/9.14  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.93/9.14  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 8.93/9.14  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.93/9.14  thf(sk_A_type, type, sk_A: $i).
% 8.93/9.14  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.93/9.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.93/9.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.93/9.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.93/9.14  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 8.93/9.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.93/9.14  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 8.93/9.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.93/9.14  thf(sk_B_type, type, sk_B: $i).
% 8.93/9.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.93/9.14  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 8.93/9.14  thf(t77_tops_1, conjecture,
% 8.93/9.14    (![A:$i]:
% 8.93/9.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.93/9.14       ( ![B:$i]:
% 8.93/9.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.93/9.14           ( ( v4_pre_topc @ B @ A ) <=>
% 8.93/9.14             ( ( k2_tops_1 @ A @ B ) =
% 8.93/9.14               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 8.93/9.14  thf(zf_stmt_0, negated_conjecture,
% 8.93/9.14    (~( ![A:$i]:
% 8.93/9.14        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.93/9.14          ( ![B:$i]:
% 8.93/9.14            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.93/9.14              ( ( v4_pre_topc @ B @ A ) <=>
% 8.93/9.14                ( ( k2_tops_1 @ A @ B ) =
% 8.93/9.14                  ( k7_subset_1 @
% 8.93/9.14                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 8.93/9.14    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 8.93/9.14  thf('0', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(involutiveness_k3_subset_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.93/9.14       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 8.93/9.14  thf('1', plain,
% 8.93/9.14      (![X35 : $i, X36 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 8.93/9.14          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 8.93/9.14      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.93/9.14  thf('2', plain,
% 8.93/9.14      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.93/9.14      inference('sup-', [status(thm)], ['0', '1'])).
% 8.93/9.14  thf('3', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(d5_subset_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.93/9.14       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 8.93/9.14  thf('4', plain,
% 8.93/9.14      (![X29 : $i, X30 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 8.93/9.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 8.93/9.14      inference('cnf', [status(esa)], [d5_subset_1])).
% 8.93/9.14  thf(redefinition_k6_subset_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 8.93/9.14  thf('5', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('6', plain,
% 8.93/9.14      (![X29 : $i, X30 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 8.93/9.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 8.93/9.14      inference('demod', [status(thm)], ['4', '5'])).
% 8.93/9.14  thf('7', plain,
% 8.93/9.14      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 8.93/9.14         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 8.93/9.14      inference('sup-', [status(thm)], ['3', '6'])).
% 8.93/9.14  thf('8', plain,
% 8.93/9.14      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.93/9.14      inference('demod', [status(thm)], ['2', '7'])).
% 8.93/9.14  thf(dt_k6_subset_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 8.93/9.14  thf('9', plain,
% 8.93/9.14      (![X33 : $i, X34 : $i]:
% 8.93/9.14         (m1_subset_1 @ (k6_subset_1 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))),
% 8.93/9.14      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 8.93/9.14  thf('10', plain,
% 8.93/9.14      (![X29 : $i, X30 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 8.93/9.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 8.93/9.14      inference('demod', [status(thm)], ['4', '5'])).
% 8.93/9.14  thf('11', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.93/9.14           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['9', '10'])).
% 8.93/9.14  thf('12', plain,
% 8.93/9.14      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.93/9.14      inference('demod', [status(thm)], ['8', '11'])).
% 8.93/9.14  thf('13', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(t3_subset, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.93/9.14  thf('14', plain,
% 8.93/9.14      (![X49 : $i, X50 : $i]:
% 8.93/9.14         ((r1_tarski @ X49 @ X50) | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t3_subset])).
% 8.93/9.14  thf('15', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.93/9.14      inference('sup-', [status(thm)], ['13', '14'])).
% 8.93/9.14  thf(t1_boole, axiom,
% 8.93/9.14    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 8.93/9.14  thf('16', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 8.93/9.14      inference('cnf', [status(esa)], [t1_boole])).
% 8.93/9.14  thf(l51_zfmisc_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.93/9.14  thf('17', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('18', plain,
% 8.93/9.14      (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ k1_xboole_0)) = (X6))),
% 8.93/9.14      inference('demod', [status(thm)], ['16', '17'])).
% 8.93/9.14  thf(t43_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 8.93/9.14       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 8.93/9.14  thf('19', plain,
% 8.93/9.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.93/9.14         ((r1_tarski @ (k4_xboole_0 @ X14 @ X15) @ X16)
% 8.93/9.14          | ~ (r1_tarski @ X14 @ (k2_xboole_0 @ X15 @ X16)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t43_xboole_1])).
% 8.93/9.14  thf('20', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('21', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('22', plain,
% 8.93/9.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.93/9.14         ((r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16)
% 8.93/9.14          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 8.93/9.14      inference('demod', [status(thm)], ['19', '20', '21'])).
% 8.93/9.14  thf('23', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (~ (r1_tarski @ X1 @ X0)
% 8.93/9.14          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['18', '22'])).
% 8.93/9.14  thf('24', plain,
% 8.93/9.14      ((r1_tarski @ (k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) @ k1_xboole_0)),
% 8.93/9.14      inference('sup-', [status(thm)], ['15', '23'])).
% 8.93/9.14  thf('25', plain,
% 8.93/9.14      (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ k1_xboole_0)) = (X6))),
% 8.93/9.14      inference('demod', [status(thm)], ['16', '17'])).
% 8.93/9.14  thf(t36_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 8.93/9.14  thf('26', plain,
% 8.93/9.14      (![X10 : $i, X11 : $i]: (r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X10)),
% 8.93/9.14      inference('cnf', [status(esa)], [t36_xboole_1])).
% 8.93/9.14  thf('27', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('28', plain,
% 8.93/9.14      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 8.93/9.14      inference('demod', [status(thm)], ['26', '27'])).
% 8.93/9.14  thf(t44_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 8.93/9.14       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 8.93/9.14  thf('29', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19))
% 8.93/9.14          | ~ (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19))),
% 8.93/9.14      inference('cnf', [status(esa)], [t44_xboole_1])).
% 8.93/9.14  thf('30', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('31', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('32', plain,
% 8.93/9.14      (![X17 : $i, X18 : $i, X19 : $i]:
% 8.93/9.14         ((r1_tarski @ X17 @ (k3_tarski @ (k2_tarski @ X18 @ X19)))
% 8.93/9.14          | ~ (r1_tarski @ (k6_subset_1 @ X17 @ X18) @ X19))),
% 8.93/9.14      inference('demod', [status(thm)], ['29', '30', '31'])).
% 8.93/9.14  thf('33', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['28', '32'])).
% 8.93/9.14  thf('34', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.93/9.14      inference('sup+', [status(thm)], ['25', '33'])).
% 8.93/9.14  thf('35', plain,
% 8.93/9.14      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 8.93/9.14      inference('demod', [status(thm)], ['26', '27'])).
% 8.93/9.14  thf(t1_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 8.93/9.14       ( r1_tarski @ A @ C ) ))).
% 8.93/9.14  thf('36', plain,
% 8.93/9.14      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.93/9.14         (~ (r1_tarski @ X7 @ X8)
% 8.93/9.14          | ~ (r1_tarski @ X8 @ X9)
% 8.93/9.14          | (r1_tarski @ X7 @ X9))),
% 8.93/9.14      inference('cnf', [status(esa)], [t1_xboole_1])).
% 8.93/9.14  thf('37', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 8.93/9.14      inference('sup-', [status(thm)], ['35', '36'])).
% 8.93/9.14  thf('38', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ k1_xboole_0 @ X1) @ X0)),
% 8.93/9.14      inference('sup-', [status(thm)], ['34', '37'])).
% 8.93/9.14  thf(t38_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 8.93/9.14       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.93/9.14  thf('39', plain,
% 8.93/9.14      (![X12 : $i, X13 : $i]:
% 8.93/9.14         (((X12) = (k1_xboole_0))
% 8.93/9.14          | ~ (r1_tarski @ X12 @ (k4_xboole_0 @ X13 @ X12)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t38_xboole_1])).
% 8.93/9.14  thf('40', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('41', plain,
% 8.93/9.14      (![X12 : $i, X13 : $i]:
% 8.93/9.14         (((X12) = (k1_xboole_0))
% 8.93/9.14          | ~ (r1_tarski @ X12 @ (k6_subset_1 @ X13 @ X12)))),
% 8.93/9.14      inference('demod', [status(thm)], ['39', '40'])).
% 8.93/9.14  thf('42', plain,
% 8.93/9.14      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['38', '41'])).
% 8.93/9.14  thf('43', plain,
% 8.93/9.14      (![X12 : $i, X13 : $i]:
% 8.93/9.14         (((X12) = (k1_xboole_0))
% 8.93/9.14          | ~ (r1_tarski @ X12 @ (k6_subset_1 @ X13 @ X12)))),
% 8.93/9.14      inference('demod', [status(thm)], ['39', '40'])).
% 8.93/9.14  thf('44', plain,
% 8.93/9.14      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['42', '43'])).
% 8.93/9.14  thf('45', plain,
% 8.93/9.14      (((k6_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['24', '44'])).
% 8.93/9.14  thf(t51_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 8.93/9.14       ( A ) ))).
% 8.93/9.14  thf('46', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k2_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ (k4_xboole_0 @ X20 @ X21))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('cnf', [status(esa)], [t51_xboole_1])).
% 8.93/9.14  thf('47', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('48', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf(commutativity_k2_tarski, axiom,
% 8.93/9.14    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 8.93/9.14  thf('49', plain,
% 8.93/9.14      (![X24 : $i, X25 : $i]:
% 8.93/9.14         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 8.93/9.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.93/9.14  thf('50', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('51', plain,
% 8.93/9.14      (((k3_tarski @ 
% 8.93/9.14         (k2_tarski @ k1_xboole_0 @ (k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A))))
% 8.93/9.14         = (sk_B))),
% 8.93/9.14      inference('sup+', [status(thm)], ['45', '50'])).
% 8.93/9.14  thf('52', plain,
% 8.93/9.14      (![X24 : $i, X25 : $i]:
% 8.93/9.14         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 8.93/9.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.93/9.14  thf('53', plain,
% 8.93/9.14      (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ k1_xboole_0)) = (X6))),
% 8.93/9.14      inference('demod', [status(thm)], ['16', '17'])).
% 8.93/9.14  thf('54', plain,
% 8.93/9.14      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.14  thf('55', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (sk_B))),
% 8.93/9.14      inference('demod', [status(thm)], ['51', '54'])).
% 8.93/9.14  thf('56', plain,
% 8.93/9.14      (![X24 : $i, X25 : $i]:
% 8.93/9.14         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 8.93/9.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.93/9.14  thf(t12_setfam_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 8.93/9.14  thf('57', plain,
% 8.93/9.14      (![X47 : $i, X48 : $i]:
% 8.93/9.14         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 8.93/9.14      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.93/9.14  thf('58', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['56', '57'])).
% 8.93/9.14  thf('59', plain,
% 8.93/9.14      (![X47 : $i, X48 : $i]:
% 8.93/9.14         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 8.93/9.14      inference('cnf', [status(esa)], [t12_setfam_1])).
% 8.93/9.14  thf('60', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['58', '59'])).
% 8.93/9.14  thf(t100_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 8.93/9.14  thf('61', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i]:
% 8.93/9.14         ((k4_xboole_0 @ X4 @ X5)
% 8.93/9.14           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.14      inference('cnf', [status(esa)], [t100_xboole_1])).
% 8.93/9.14  thf('62', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('63', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X4 @ X5)
% 8.93/9.14           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.14      inference('demod', [status(thm)], ['61', '62'])).
% 8.93/9.14  thf('64', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X0 @ X1)
% 8.93/9.14           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['60', '63'])).
% 8.93/9.14  thf('65', plain,
% 8.93/9.14      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 8.93/9.14         = (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 8.93/9.14      inference('sup+', [status(thm)], ['55', '64'])).
% 8.93/9.14  thf('66', plain,
% 8.93/9.14      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.93/9.14      inference('demod', [status(thm)], ['12', '65'])).
% 8.93/9.14  thf('67', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(dt_k2_tops_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( ( l1_pre_topc @ A ) & 
% 8.93/9.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.93/9.14       ( m1_subset_1 @
% 8.93/9.14         ( k2_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.93/9.14  thf('68', plain,
% 8.93/9.14      (![X54 : $i, X55 : $i]:
% 8.93/9.14         (~ (l1_pre_topc @ X54)
% 8.93/9.14          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 8.93/9.14          | (m1_subset_1 @ (k2_tops_1 @ X54 @ X55) @ 
% 8.93/9.14             (k1_zfmisc_1 @ (u1_struct_0 @ X54))))),
% 8.93/9.14      inference('cnf', [status(esa)], [dt_k2_tops_1])).
% 8.93/9.14  thf('69', plain,
% 8.93/9.14      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.93/9.14         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.93/9.14        | ~ (l1_pre_topc @ sk_A))),
% 8.93/9.14      inference('sup-', [status(thm)], ['67', '68'])).
% 8.93/9.14  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('71', plain,
% 8.93/9.14      ((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 8.93/9.14        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('demod', [status(thm)], ['69', '70'])).
% 8.93/9.14  thf('72', plain,
% 8.93/9.14      (![X33 : $i, X34 : $i]:
% 8.93/9.14         (m1_subset_1 @ (k6_subset_1 @ X33 @ X34) @ (k1_zfmisc_1 @ X33))),
% 8.93/9.14      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 8.93/9.14  thf(redefinition_k4_subset_1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 8.93/9.14         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 8.93/9.14       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 8.93/9.14  thf('73', plain,
% 8.93/9.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.93/9.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 8.93/9.14          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 8.93/9.14  thf('74', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('75', plain,
% 8.93/9.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.93/9.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 8.93/9.14          | ((k4_subset_1 @ X38 @ X37 @ X39)
% 8.93/9.14              = (k3_tarski @ (k2_tarski @ X37 @ X39))))),
% 8.93/9.14      inference('demod', [status(thm)], ['73', '74'])).
% 8.93/9.14  thf('76', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         (((k4_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1) @ X2)
% 8.93/9.14            = (k3_tarski @ (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ X2)))
% 8.93/9.14          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['72', '75'])).
% 8.93/9.14  thf('77', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14           (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 8.93/9.14           (k2_tops_1 @ sk_A @ sk_B))
% 8.93/9.14           = (k3_tarski @ 
% 8.93/9.14              (k2_tarski @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 8.93/9.14               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('sup-', [status(thm)], ['71', '76'])).
% 8.93/9.14  thf('78', plain,
% 8.93/9.14      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.93/9.14         = (k3_tarski @ 
% 8.93/9.14            (k2_tarski @ 
% 8.93/9.14             (k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14              (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 8.93/9.14             (k2_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('sup+', [status(thm)], ['66', '77'])).
% 8.93/9.14  thf('79', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(t65_tops_1, axiom,
% 8.93/9.14    (![A:$i]:
% 8.93/9.14     ( ( l1_pre_topc @ A ) =>
% 8.93/9.14       ( ![B:$i]:
% 8.93/9.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.93/9.14           ( ( k2_pre_topc @ A @ B ) =
% 8.93/9.14             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.93/9.14  thf('80', plain,
% 8.93/9.14      (![X60 : $i, X61 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 8.93/9.14          | ((k2_pre_topc @ X61 @ X60)
% 8.93/9.14              = (k4_subset_1 @ (u1_struct_0 @ X61) @ X60 @ 
% 8.93/9.14                 (k2_tops_1 @ X61 @ X60)))
% 8.93/9.14          | ~ (l1_pre_topc @ X61))),
% 8.93/9.14      inference('cnf', [status(esa)], [t65_tops_1])).
% 8.93/9.14  thf('81', plain,
% 8.93/9.14      ((~ (l1_pre_topc @ sk_A)
% 8.93/9.14        | ((k2_pre_topc @ sk_A @ sk_B)
% 8.93/9.14            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('sup-', [status(thm)], ['79', '80'])).
% 8.93/9.14  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('83', plain,
% 8.93/9.14      (((k2_pre_topc @ sk_A @ sk_B)
% 8.93/9.14         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.14      inference('demod', [status(thm)], ['81', '82'])).
% 8.93/9.14  thf('84', plain,
% 8.93/9.14      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14             (k1_tops_1 @ sk_A @ sk_B)))
% 8.93/9.14        | (v4_pre_topc @ sk_B @ sk_A))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('85', plain,
% 8.93/9.14      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.93/9.14      inference('split', [status(esa)], ['84'])).
% 8.93/9.14  thf('86', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(t52_pre_topc, axiom,
% 8.93/9.14    (![A:$i]:
% 8.93/9.14     ( ( l1_pre_topc @ A ) =>
% 8.93/9.14       ( ![B:$i]:
% 8.93/9.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.93/9.14           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 8.93/9.14             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 8.93/9.14               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 8.93/9.14  thf('87', plain,
% 8.93/9.14      (![X52 : $i, X53 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (u1_struct_0 @ X53)))
% 8.93/9.14          | ~ (v4_pre_topc @ X52 @ X53)
% 8.93/9.14          | ((k2_pre_topc @ X53 @ X52) = (X52))
% 8.93/9.14          | ~ (l1_pre_topc @ X53))),
% 8.93/9.14      inference('cnf', [status(esa)], [t52_pre_topc])).
% 8.93/9.14  thf('88', plain,
% 8.93/9.14      ((~ (l1_pre_topc @ sk_A)
% 8.93/9.14        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B))
% 8.93/9.14        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 8.93/9.14      inference('sup-', [status(thm)], ['86', '87'])).
% 8.93/9.14  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('90', plain,
% 8.93/9.14      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)) | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 8.93/9.14      inference('demod', [status(thm)], ['88', '89'])).
% 8.93/9.14  thf('91', plain,
% 8.93/9.14      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 8.93/9.14         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['85', '90'])).
% 8.93/9.14  thf('92', plain,
% 8.93/9.14      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14              (k1_tops_1 @ sk_A @ sk_B)))
% 8.93/9.14        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('93', plain,
% 8.93/9.14      (~
% 8.93/9.14       (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 8.93/9.14       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 8.93/9.14      inference('split', [status(esa)], ['92'])).
% 8.93/9.14  thf('94', plain,
% 8.93/9.14      (((k2_pre_topc @ sk_A @ sk_B)
% 8.93/9.14         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.14      inference('demod', [status(thm)], ['81', '82'])).
% 8.93/9.14  thf('95', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(redefinition_k7_subset_1, axiom,
% 8.93/9.14    (![A:$i,B:$i,C:$i]:
% 8.93/9.14     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.93/9.14       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.93/9.14  thf('96', plain,
% 8.93/9.14      (![X42 : $i, X43 : $i, X44 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 8.93/9.14          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k4_xboole_0 @ X42 @ X44)))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.93/9.14  thf('97', plain,
% 8.93/9.14      (![X40 : $i, X41 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X40 @ X41) = (k4_xboole_0 @ X40 @ X41))),
% 8.93/9.14      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 8.93/9.14  thf('98', plain,
% 8.93/9.14      (![X42 : $i, X43 : $i, X44 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 8.93/9.14          | ((k7_subset_1 @ X43 @ X42 @ X44) = (k6_subset_1 @ X42 @ X44)))),
% 8.93/9.14      inference('demod', [status(thm)], ['96', '97'])).
% 8.93/9.14  thf('99', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.93/9.14           = (k6_subset_1 @ sk_B @ X0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['95', '98'])).
% 8.93/9.14  thf('100', plain,
% 8.93/9.14      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14             (k1_tops_1 @ sk_A @ sk_B))))
% 8.93/9.14         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.14      inference('split', [status(esa)], ['84'])).
% 8.93/9.14  thf('101', plain,
% 8.93/9.14      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          = (k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.93/9.14         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.14      inference('sup+', [status(thm)], ['99', '100'])).
% 8.93/9.14  thf('102', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 8.93/9.14      inference('sup-', [status(thm)], ['13', '14'])).
% 8.93/9.14  thf('103', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         ((r1_tarski @ (k6_subset_1 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 8.93/9.14      inference('sup-', [status(thm)], ['35', '36'])).
% 8.93/9.14  thf('104', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         (r1_tarski @ (k6_subset_1 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 8.93/9.14      inference('sup-', [status(thm)], ['102', '103'])).
% 8.93/9.14  thf('105', plain,
% 8.93/9.14      (![X49 : $i, X51 : $i]:
% 8.93/9.14         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t3_subset])).
% 8.93/9.14  thf('106', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         (m1_subset_1 @ (k6_subset_1 @ sk_B @ X0) @ 
% 8.93/9.14          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['104', '105'])).
% 8.93/9.14  thf('107', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('108', plain,
% 8.93/9.14      (![X37 : $i, X38 : $i, X39 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 8.93/9.14          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 8.93/9.14          | ((k4_subset_1 @ X38 @ X37 @ X39)
% 8.93/9.14              = (k3_tarski @ (k2_tarski @ X37 @ X39))))),
% 8.93/9.14      inference('demod', [status(thm)], ['73', '74'])).
% 8.93/9.14  thf('109', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.93/9.14            = (k3_tarski @ (k2_tarski @ sk_B @ X0)))
% 8.93/9.14          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 8.93/9.14      inference('sup-', [status(thm)], ['107', '108'])).
% 8.93/9.14  thf('110', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14           (k6_subset_1 @ sk_B @ X0))
% 8.93/9.14           = (k3_tarski @ (k2_tarski @ sk_B @ (k6_subset_1 @ sk_B @ X0))))),
% 8.93/9.14      inference('sup-', [status(thm)], ['106', '109'])).
% 8.93/9.14  thf('111', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf(t6_xboole_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 8.93/9.14  thf('112', plain,
% 8.93/9.14      (![X22 : $i, X23 : $i]:
% 8.93/9.14         ((k2_xboole_0 @ X22 @ (k2_xboole_0 @ X22 @ X23))
% 8.93/9.14           = (k2_xboole_0 @ X22 @ X23))),
% 8.93/9.14      inference('cnf', [status(esa)], [t6_xboole_1])).
% 8.93/9.14  thf('113', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('114', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('115', plain,
% 8.93/9.14      (![X26 : $i, X27 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X26 @ X27)) = (k2_xboole_0 @ X26 @ X27))),
% 8.93/9.14      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 8.93/9.14  thf('116', plain,
% 8.93/9.14      (![X22 : $i, X23 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ X22 @ (k3_tarski @ (k2_tarski @ X22 @ X23))))
% 8.93/9.14           = (k3_tarski @ (k2_tarski @ X22 @ X23)))),
% 8.93/9.14      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 8.93/9.14  thf('117', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ X0))
% 8.93/9.14           = (k3_tarski @ 
% 8.93/9.14              (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))))),
% 8.93/9.14      inference('sup+', [status(thm)], ['111', '116'])).
% 8.93/9.14  thf('118', plain,
% 8.93/9.14      (![X24 : $i, X25 : $i]:
% 8.93/9.14         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 8.93/9.14      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.93/9.14  thf('119', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X0 @ (k6_subset_1 @ X0 @ X1)))
% 8.93/9.14           = (k3_tarski @ 
% 8.93/9.14              (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X1))))),
% 8.93/9.14      inference('demod', [status(thm)], ['117', '118'])).
% 8.93/9.14  thf('120', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('121', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_tarski @ (k2_tarski @ X1 @ (k6_subset_1 @ X1 @ X0))) = (X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['119', '120'])).
% 8.93/9.14  thf('122', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14           (k6_subset_1 @ sk_B @ X0)) = (sk_B))),
% 8.93/9.14      inference('demod', [status(thm)], ['110', '121'])).
% 8.93/9.14  thf('123', plain,
% 8.93/9.14      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 8.93/9.14          = (sk_B)))
% 8.93/9.14         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.14      inference('sup+', [status(thm)], ['101', '122'])).
% 8.93/9.14  thf('124', plain,
% 8.93/9.14      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 8.93/9.14         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.14      inference('sup+', [status(thm)], ['94', '123'])).
% 8.93/9.14  thf('125', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(fc1_tops_1, axiom,
% 8.93/9.14    (![A:$i,B:$i]:
% 8.93/9.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 8.93/9.14         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.93/9.14       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 8.93/9.14  thf('126', plain,
% 8.93/9.14      (![X56 : $i, X57 : $i]:
% 8.93/9.14         (~ (l1_pre_topc @ X56)
% 8.93/9.14          | ~ (v2_pre_topc @ X56)
% 8.93/9.14          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 8.93/9.14          | (v4_pre_topc @ (k2_pre_topc @ X56 @ X57) @ X56))),
% 8.93/9.14      inference('cnf', [status(esa)], [fc1_tops_1])).
% 8.93/9.14  thf('127', plain,
% 8.93/9.14      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 8.93/9.14        | ~ (v2_pre_topc @ sk_A)
% 8.93/9.14        | ~ (l1_pre_topc @ sk_A))),
% 8.93/9.14      inference('sup-', [status(thm)], ['125', '126'])).
% 8.93/9.14  thf('128', plain, ((v2_pre_topc @ sk_A)),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('129', plain, ((l1_pre_topc @ sk_A)),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('130', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 8.93/9.14      inference('demod', [status(thm)], ['127', '128', '129'])).
% 8.93/9.14  thf('131', plain,
% 8.93/9.14      (((v4_pre_topc @ sk_B @ sk_A))
% 8.93/9.14         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.14      inference('sup+', [status(thm)], ['124', '130'])).
% 8.93/9.14  thf('132', plain,
% 8.93/9.14      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 8.93/9.14      inference('split', [status(esa)], ['92'])).
% 8.93/9.14  thf('133', plain,
% 8.93/9.14      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 8.93/9.14       ~
% 8.93/9.14       (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14             (k1_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('sup-', [status(thm)], ['131', '132'])).
% 8.93/9.14  thf('134', plain,
% 8.93/9.14      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 8.93/9.14       (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.14          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14             (k1_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('split', [status(esa)], ['84'])).
% 8.93/9.14  thf('135', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 8.93/9.14      inference('sat_resolution*', [status(thm)], ['93', '133', '134'])).
% 8.93/9.14  thf('136', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 8.93/9.14      inference('simpl_trail', [status(thm)], ['91', '135'])).
% 8.93/9.14  thf('137', plain,
% 8.93/9.14      (((sk_B)
% 8.93/9.14         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14            (k2_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.14      inference('demod', [status(thm)], ['83', '136'])).
% 8.93/9.14  thf('138', plain,
% 8.93/9.14      (((k6_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 8.93/9.14         (k5_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 8.93/9.14      inference('demod', [status(thm)], ['12', '65'])).
% 8.93/9.14  thf('139', plain,
% 8.93/9.14      (((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('demod', [status(thm)], ['78', '137', '138'])).
% 8.93/9.14  thf('140', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['28', '32'])).
% 8.93/9.14  thf('141', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (~ (r1_tarski @ X1 @ X0)
% 8.93/9.14          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['18', '22'])).
% 8.93/9.14  thf('142', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (r1_tarski @ 
% 8.93/9.14          (k6_subset_1 @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0))) @ 
% 8.93/9.14          k1_xboole_0)),
% 8.93/9.14      inference('sup-', [status(thm)], ['140', '141'])).
% 8.93/9.14  thf('143', plain,
% 8.93/9.14      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['42', '43'])).
% 8.93/9.14  thf('144', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))
% 8.93/9.14           = (k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['142', '143'])).
% 8.93/9.14  thf('145', plain,
% 8.93/9.14      (((k6_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['139', '144'])).
% 8.93/9.14  thf('146', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['58', '59'])).
% 8.93/9.14  thf('147', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('148', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 8.93/9.14           = (X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['146', '147'])).
% 8.93/9.14  thf('149', plain,
% 8.93/9.14      (((k3_tarski @ 
% 8.93/9.14         (k2_tarski @ k1_xboole_0 @ 
% 8.93/9.14          (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 8.93/9.14         = (k2_tops_1 @ sk_A @ sk_B))),
% 8.93/9.14      inference('sup+', [status(thm)], ['145', '148'])).
% 8.93/9.14  thf('150', plain,
% 8.93/9.14      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf(t74_tops_1, axiom,
% 8.93/9.14    (![A:$i]:
% 8.93/9.14     ( ( l1_pre_topc @ A ) =>
% 8.93/9.14       ( ![B:$i]:
% 8.93/9.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.93/9.14           ( ( k1_tops_1 @ A @ B ) =
% 8.93/9.14             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 8.93/9.14  thf('151', plain,
% 8.93/9.14      (![X62 : $i, X63 : $i]:
% 8.93/9.14         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 8.93/9.14          | ((k1_tops_1 @ X63 @ X62)
% 8.93/9.14              = (k7_subset_1 @ (u1_struct_0 @ X63) @ X62 @ 
% 8.93/9.14                 (k2_tops_1 @ X63 @ X62)))
% 8.93/9.14          | ~ (l1_pre_topc @ X63))),
% 8.93/9.14      inference('cnf', [status(esa)], [t74_tops_1])).
% 8.93/9.14  thf('152', plain,
% 8.93/9.14      ((~ (l1_pre_topc @ sk_A)
% 8.93/9.14        | ((k1_tops_1 @ sk_A @ sk_B)
% 8.93/9.14            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.14               (k2_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.14      inference('sup-', [status(thm)], ['150', '151'])).
% 8.93/9.14  thf('153', plain, ((l1_pre_topc @ sk_A)),
% 8.93/9.14      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.93/9.14  thf('154', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.93/9.14           = (k6_subset_1 @ sk_B @ X0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['95', '98'])).
% 8.93/9.14  thf('155', plain,
% 8.93/9.14      (((k1_tops_1 @ sk_A @ sk_B)
% 8.93/9.14         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.14      inference('demod', [status(thm)], ['152', '153', '154'])).
% 8.93/9.14  thf('156', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.93/9.14           = (k6_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['9', '10'])).
% 8.93/9.14  thf('157', plain,
% 8.93/9.14      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 8.93/9.14      inference('demod', [status(thm)], ['26', '27'])).
% 8.93/9.14  thf('158', plain,
% 8.93/9.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.93/9.14         ((r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16)
% 8.93/9.14          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 8.93/9.14      inference('demod', [status(thm)], ['19', '20', '21'])).
% 8.93/9.14  thf('159', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         (r1_tarski @ 
% 8.93/9.14          (k6_subset_1 @ 
% 8.93/9.14           (k6_subset_1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 8.93/9.14          X0)),
% 8.93/9.14      inference('sup-', [status(thm)], ['157', '158'])).
% 8.93/9.14  thf('160', plain,
% 8.93/9.14      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['42', '43'])).
% 8.93/9.14  thf('161', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k6_subset_1 @ 
% 8.93/9.14           (k6_subset_1 @ (k3_tarski @ (k2_tarski @ X0 @ k1_xboole_0)) @ X1) @ 
% 8.93/9.14           X0) = (k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['159', '160'])).
% 8.93/9.14  thf('162', plain,
% 8.93/9.14      (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ k1_xboole_0)) = (X6))),
% 8.93/9.14      inference('demod', [status(thm)], ['16', '17'])).
% 8.93/9.14  thf('163', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 8.93/9.14      inference('demod', [status(thm)], ['161', '162'])).
% 8.93/9.14  thf('164', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('165', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ k1_xboole_0 @ 
% 8.93/9.14            (k3_xboole_0 @ (k6_subset_1 @ X1 @ X0) @ X1)))
% 8.93/9.14           = (k6_subset_1 @ X1 @ X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['163', '164'])).
% 8.93/9.14  thf('166', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['58', '59'])).
% 8.93/9.14  thf('167', plain,
% 8.93/9.14      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.14  thf('168', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 8.93/9.14           = (k6_subset_1 @ X1 @ X0))),
% 8.93/9.14      inference('demod', [status(thm)], ['165', '166', '167'])).
% 8.93/9.14  thf('169', plain,
% 8.93/9.14      (![X4 : $i, X5 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X4 @ X5)
% 8.93/9.14           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.14      inference('demod', [status(thm)], ['61', '62'])).
% 8.93/9.14  thf('170', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k6_subset_1 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 8.93/9.14           = (k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0)))),
% 8.93/9.14      inference('sup+', [status(thm)], ['168', '169'])).
% 8.93/9.14  thf('171', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.93/9.14           = (k5_xboole_0 @ X0 @ (k6_subset_1 @ X0 @ X1)))),
% 8.93/9.14      inference('demod', [status(thm)], ['156', '170'])).
% 8.93/9.14  thf('172', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('173', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['28', '32'])).
% 8.93/9.14  thf('174', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 8.93/9.14      inference('sup+', [status(thm)], ['172', '173'])).
% 8.93/9.14  thf('175', plain,
% 8.93/9.14      (![X49 : $i, X51 : $i]:
% 8.93/9.14         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t3_subset])).
% 8.93/9.14  thf('176', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['174', '175'])).
% 8.93/9.14  thf('177', plain,
% 8.93/9.14      (![X35 : $i, X36 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 8.93/9.14          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 8.93/9.14      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.93/9.14  thf('178', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 8.93/9.14           = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('sup-', [status(thm)], ['176', '177'])).
% 8.93/9.14  thf('179', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['174', '175'])).
% 8.93/9.14  thf('180', plain,
% 8.93/9.14      (![X29 : $i, X30 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 8.93/9.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 8.93/9.14      inference('demod', [status(thm)], ['4', '5'])).
% 8.93/9.14  thf('181', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 8.93/9.14           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 8.93/9.14      inference('sup-', [status(thm)], ['179', '180'])).
% 8.93/9.14  thf('182', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 8.93/9.14           = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('demod', [status(thm)], ['178', '181'])).
% 8.93/9.14  thf('183', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 8.93/9.14      inference('sup+', [status(thm)], ['172', '173'])).
% 8.93/9.14  thf('184', plain,
% 8.93/9.14      (![X14 : $i, X15 : $i, X16 : $i]:
% 8.93/9.14         ((r1_tarski @ (k6_subset_1 @ X14 @ X15) @ X16)
% 8.93/9.14          | ~ (r1_tarski @ X14 @ (k3_tarski @ (k2_tarski @ X15 @ X16))))),
% 8.93/9.14      inference('demod', [status(thm)], ['19', '20', '21'])).
% 8.93/9.14  thf('185', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.14         (r1_tarski @ 
% 8.93/9.14          (k6_subset_1 @ 
% 8.93/9.14           (k3_xboole_0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)) @ X2) @ X1) @ 
% 8.93/9.14          X0)),
% 8.93/9.14      inference('sup-', [status(thm)], ['183', '184'])).
% 8.93/9.14  thf('186', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.93/9.14      inference('sup+', [status(thm)], ['25', '33'])).
% 8.93/9.14  thf('187', plain,
% 8.93/9.14      (![X49 : $i, X51 : $i]:
% 8.93/9.14         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 8.93/9.14      inference('cnf', [status(esa)], [t3_subset])).
% 8.93/9.14  thf('188', plain,
% 8.93/9.14      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['186', '187'])).
% 8.93/9.14  thf('189', plain,
% 8.93/9.14      (![X35 : $i, X36 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 8.93/9.14          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 8.93/9.14      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 8.93/9.14  thf('190', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['188', '189'])).
% 8.93/9.14  thf('191', plain,
% 8.93/9.14      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['186', '187'])).
% 8.93/9.14  thf('192', plain,
% 8.93/9.14      (![X29 : $i, X30 : $i]:
% 8.93/9.14         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 8.93/9.14          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 8.93/9.14      inference('demod', [status(thm)], ['4', '5'])).
% 8.93/9.14  thf('193', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k6_subset_1 @ X0 @ k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['191', '192'])).
% 8.93/9.14  thf('194', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 8.93/9.14      inference('demod', [status(thm)], ['190', '193'])).
% 8.93/9.14  thf('195', plain,
% 8.93/9.14      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.93/9.14      inference('sup-', [status(thm)], ['38', '41'])).
% 8.93/9.14  thf('196', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('197', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 8.93/9.14           = (k1_xboole_0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['195', '196'])).
% 8.93/9.14  thf('198', plain,
% 8.93/9.14      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.14  thf('199', plain,
% 8.93/9.14      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 8.93/9.14      inference('demod', [status(thm)], ['197', '198'])).
% 8.93/9.14  thf('200', plain,
% 8.93/9.14      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.14      inference('sup+', [status(thm)], ['58', '59'])).
% 8.93/9.14  thf('201', plain,
% 8.93/9.14      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 8.93/9.14      inference('sup+', [status(thm)], ['199', '200'])).
% 8.93/9.14  thf('202', plain,
% 8.93/9.14      (![X20 : $i, X21 : $i]:
% 8.93/9.14         ((k3_tarski @ 
% 8.93/9.14           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.14           = (X20))),
% 8.93/9.14      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.14  thf('203', plain,
% 8.93/9.14      (![X0 : $i]:
% 8.93/9.15         ((k3_tarski @ 
% 8.93/9.15           (k2_tarski @ (k6_subset_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)) = (
% 8.93/9.15           X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['201', '202'])).
% 8.93/9.15  thf('204', plain,
% 8.93/9.15      (![X24 : $i, X25 : $i]:
% 8.93/9.15         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 8.93/9.15      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 8.93/9.15  thf('205', plain,
% 8.93/9.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.15  thf('206', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 8.93/9.15      inference('demod', [status(thm)], ['203', '204', '205'])).
% 8.93/9.15  thf('207', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 8.93/9.15      inference('demod', [status(thm)], ['194', '206'])).
% 8.93/9.15  thf(d3_tarski, axiom,
% 8.93/9.15    (![A:$i,B:$i]:
% 8.93/9.15     ( ( r1_tarski @ A @ B ) <=>
% 8.93/9.15       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.93/9.15  thf('208', plain,
% 8.93/9.15      (![X1 : $i, X3 : $i]:
% 8.93/9.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.93/9.15      inference('cnf', [status(esa)], [d3_tarski])).
% 8.93/9.15  thf('209', plain,
% 8.93/9.15      (![X1 : $i, X3 : $i]:
% 8.93/9.15         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.93/9.15      inference('cnf', [status(esa)], [d3_tarski])).
% 8.93/9.15  thf('210', plain,
% 8.93/9.15      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['208', '209'])).
% 8.93/9.15  thf('211', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.93/9.15      inference('simplify', [status(thm)], ['210'])).
% 8.93/9.15  thf('212', plain,
% 8.93/9.15      (![X49 : $i, X51 : $i]:
% 8.93/9.15         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 8.93/9.15      inference('cnf', [status(esa)], [t3_subset])).
% 8.93/9.15  thf('213', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['211', '212'])).
% 8.93/9.15  thf('214', plain,
% 8.93/9.15      (![X29 : $i, X30 : $i]:
% 8.93/9.15         (((k3_subset_1 @ X29 @ X30) = (k6_subset_1 @ X29 @ X30))
% 8.93/9.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 8.93/9.15      inference('demod', [status(thm)], ['4', '5'])).
% 8.93/9.15  thf('215', plain,
% 8.93/9.15      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k6_subset_1 @ X0 @ X0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['213', '214'])).
% 8.93/9.15  thf('216', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['207', '215'])).
% 8.93/9.15  thf('217', plain,
% 8.93/9.15      (![X20 : $i, X21 : $i]:
% 8.93/9.15         ((k3_tarski @ 
% 8.93/9.15           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.15           = (X20))),
% 8.93/9.15      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.15  thf('218', plain,
% 8.93/9.15      (![X0 : $i]:
% 8.93/9.15         ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ X0)))
% 8.93/9.15           = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['216', '217'])).
% 8.93/9.15  thf('219', plain,
% 8.93/9.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.15  thf('220', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 8.93/9.15      inference('demod', [status(thm)], ['218', '219'])).
% 8.93/9.15  thf('221', plain,
% 8.93/9.15      (![X4 : $i, X5 : $i]:
% 8.93/9.15         ((k6_subset_1 @ X4 @ X5)
% 8.93/9.15           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.15      inference('demod', [status(thm)], ['61', '62'])).
% 8.93/9.15  thf('222', plain,
% 8.93/9.15      (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['220', '221'])).
% 8.93/9.15  thf('223', plain, (![X0 : $i]: ((k1_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['207', '215'])).
% 8.93/9.15  thf('224', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['222', '223'])).
% 8.93/9.15  thf('225', plain,
% 8.93/9.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.93/9.15      inference('sup-', [status(thm)], ['42', '43'])).
% 8.93/9.15  thf('226', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 8.93/9.15      inference('sup-', [status(thm)], ['224', '225'])).
% 8.93/9.15  thf('227', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.93/9.15         ((k6_subset_1 @ 
% 8.93/9.15           (k3_xboole_0 @ 
% 8.93/9.15            (k3_tarski @ (k2_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))) @ X2) @ 
% 8.93/9.15           X1) = (k1_xboole_0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['185', '226'])).
% 8.93/9.15  thf('228', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['222', '223'])).
% 8.93/9.15  thf('229', plain,
% 8.93/9.15      (![X6 : $i]: ((k3_tarski @ (k2_tarski @ X6 @ k1_xboole_0)) = (X6))),
% 8.93/9.15      inference('demod', [status(thm)], ['16', '17'])).
% 8.93/9.15  thf('230', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k3_tarski @ (k2_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0))) = (X1))),
% 8.93/9.15      inference('sup+', [status(thm)], ['228', '229'])).
% 8.93/9.15  thf('231', plain,
% 8.93/9.15      (![X1 : $i, X2 : $i]:
% 8.93/9.15         ((k6_subset_1 @ (k3_xboole_0 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 8.93/9.15      inference('demod', [status(thm)], ['227', '230'])).
% 8.93/9.15  thf('232', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k3_tarski @ 
% 8.93/9.15           (k2_tarski @ (k6_subset_1 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))
% 8.93/9.15           = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['146', '147'])).
% 8.93/9.15  thf('233', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k3_tarski @ 
% 8.93/9.15           (k2_tarski @ k1_xboole_0 @ 
% 8.93/9.15            (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))
% 8.93/9.15           = (k3_xboole_0 @ X1 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['231', '232'])).
% 8.93/9.15  thf('234', plain,
% 8.93/9.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.15  thf('235', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.93/9.15           = (k3_xboole_0 @ X1 @ X0))),
% 8.93/9.15      inference('demod', [status(thm)], ['233', '234'])).
% 8.93/9.15  thf('236', plain,
% 8.93/9.15      (![X4 : $i, X5 : $i]:
% 8.93/9.15         ((k6_subset_1 @ X4 @ X5)
% 8.93/9.15           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.15      inference('demod', [status(thm)], ['61', '62'])).
% 8.93/9.15  thf('237', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.93/9.15           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 8.93/9.15      inference('sup+', [status(thm)], ['235', '236'])).
% 8.93/9.15  thf('238', plain,
% 8.93/9.15      (![X4 : $i, X5 : $i]:
% 8.93/9.15         ((k6_subset_1 @ X4 @ X5)
% 8.93/9.15           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.15      inference('demod', [status(thm)], ['61', '62'])).
% 8.93/9.15  thf('239', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k6_subset_1 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 8.93/9.15           = (k6_subset_1 @ X1 @ X0))),
% 8.93/9.15      inference('demod', [status(thm)], ['237', '238'])).
% 8.93/9.15  thf('240', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k3_subset_1 @ X0 @ (k6_subset_1 @ X0 @ X1))
% 8.93/9.15           = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.15      inference('demod', [status(thm)], ['182', '239'])).
% 8.93/9.15  thf('241', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         ((k5_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 8.93/9.15           = (k3_xboole_0 @ X1 @ X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['171', '240'])).
% 8.93/9.15  thf('242', plain,
% 8.93/9.15      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.93/9.15         = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.15      inference('sup+', [status(thm)], ['155', '241'])).
% 8.93/9.15  thf('243', plain,
% 8.93/9.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.15  thf('244', plain,
% 8.93/9.15      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.93/9.15         = (k2_tops_1 @ sk_A @ sk_B))),
% 8.93/9.15      inference('demod', [status(thm)], ['149', '242', '243'])).
% 8.93/9.15  thf('245', plain,
% 8.93/9.15      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.15          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.15              (k1_tops_1 @ sk_A @ sk_B))))
% 8.93/9.15         <= (~
% 8.93/9.15             (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.15                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.15                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.15      inference('split', [status(esa)], ['92'])).
% 8.93/9.15  thf('246', plain,
% 8.93/9.15      (![X0 : $i]:
% 8.93/9.15         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.93/9.15           = (k6_subset_1 @ sk_B @ X0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['95', '98'])).
% 8.93/9.15  thf('247', plain,
% 8.93/9.15      (((k1_tops_1 @ sk_A @ sk_B)
% 8.93/9.15         = (k6_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.15      inference('demod', [status(thm)], ['152', '153', '154'])).
% 8.93/9.15  thf('248', plain,
% 8.93/9.15      (![X10 : $i, X11 : $i]: (r1_tarski @ (k6_subset_1 @ X10 @ X11) @ X10)),
% 8.93/9.15      inference('demod', [status(thm)], ['26', '27'])).
% 8.93/9.15  thf('249', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 8.93/9.15      inference('sup+', [status(thm)], ['247', '248'])).
% 8.93/9.15  thf('250', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]:
% 8.93/9.15         (~ (r1_tarski @ X1 @ X0)
% 8.93/9.15          | (r1_tarski @ (k6_subset_1 @ X1 @ X0) @ k1_xboole_0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['18', '22'])).
% 8.93/9.15  thf('251', plain,
% 8.93/9.15      ((r1_tarski @ (k6_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) @ 
% 8.93/9.15        k1_xboole_0)),
% 8.93/9.15      inference('sup-', [status(thm)], ['249', '250'])).
% 8.93/9.15  thf('252', plain,
% 8.93/9.15      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 8.93/9.15      inference('sup-', [status(thm)], ['42', '43'])).
% 8.93/9.15  thf('253', plain,
% 8.93/9.15      (((k6_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 8.93/9.15      inference('sup-', [status(thm)], ['251', '252'])).
% 8.93/9.15  thf('254', plain,
% 8.93/9.15      (![X20 : $i, X21 : $i]:
% 8.93/9.15         ((k3_tarski @ 
% 8.93/9.15           (k2_tarski @ (k6_subset_1 @ X20 @ X21) @ (k3_xboole_0 @ X20 @ X21)))
% 8.93/9.15           = (X20))),
% 8.93/9.15      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 8.93/9.15  thf('255', plain,
% 8.93/9.15      (((k3_tarski @ 
% 8.93/9.15         (k2_tarski @ k1_xboole_0 @ 
% 8.93/9.15          (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 8.93/9.15         = (k1_tops_1 @ sk_A @ sk_B))),
% 8.93/9.15      inference('sup+', [status(thm)], ['253', '254'])).
% 8.93/9.15  thf('256', plain,
% 8.93/9.15      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 8.93/9.15      inference('sup+', [status(thm)], ['58', '59'])).
% 8.93/9.15  thf('257', plain,
% 8.93/9.15      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 8.93/9.15      inference('sup+', [status(thm)], ['52', '53'])).
% 8.93/9.15  thf('258', plain,
% 8.93/9.15      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.93/9.15         = (k1_tops_1 @ sk_A @ sk_B))),
% 8.93/9.15      inference('demod', [status(thm)], ['255', '256', '257'])).
% 8.93/9.15  thf('259', plain,
% 8.93/9.15      (![X4 : $i, X5 : $i]:
% 8.93/9.15         ((k6_subset_1 @ X4 @ X5)
% 8.93/9.15           = (k5_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)))),
% 8.93/9.15      inference('demod', [status(thm)], ['61', '62'])).
% 8.93/9.15  thf('260', plain,
% 8.93/9.15      (((k6_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 8.93/9.15         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.15      inference('sup+', [status(thm)], ['258', '259'])).
% 8.93/9.15  thf('261', plain,
% 8.93/9.15      ((((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.15          != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 8.93/9.15         <= (~
% 8.93/9.15             (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.15                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.15                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 8.93/9.15      inference('demod', [status(thm)], ['245', '246', '260'])).
% 8.93/9.15  thf('262', plain,
% 8.93/9.15      (~
% 8.93/9.15       (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.15          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 8.93/9.15             (k1_tops_1 @ sk_A @ sk_B))))),
% 8.93/9.15      inference('sat_resolution*', [status(thm)], ['93', '133'])).
% 8.93/9.15  thf('263', plain,
% 8.93/9.15      (((k2_tops_1 @ sk_A @ sk_B)
% 8.93/9.15         != (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 8.93/9.15      inference('simpl_trail', [status(thm)], ['261', '262'])).
% 8.93/9.15  thf('264', plain, ($false),
% 8.93/9.15      inference('simplify_reflect-', [status(thm)], ['244', '263'])).
% 8.93/9.15  
% 8.93/9.15  % SZS output end Refutation
% 8.93/9.15  
% 8.93/9.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
