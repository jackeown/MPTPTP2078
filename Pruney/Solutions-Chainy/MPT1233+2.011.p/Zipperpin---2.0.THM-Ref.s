%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qj7gWg5bjt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:50 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 347 expanded)
%              Number of leaves         :   45 ( 130 expanded)
%              Depth                    :   19
%              Number of atoms          :  740 (2232 expanded)
%              Number of equality atoms :   65 ( 229 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_subset_1 @ X45 @ ( k3_subset_1 @ X45 @ X44 ) )
        = X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X41 @ X42 )
        = ( k4_xboole_0 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X9 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X47 @ X48 ) )
      = ( k3_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k1_setfam_1 @ ( k2_tarski @ X7 @ X8 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X10: $i] :
      ( ( k5_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','15'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('17',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X43 ) @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('18',plain,(
    ! [X40: $i] :
      ( ( k2_subset_1 @ X40 )
      = X40 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('19',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k3_subset_1 @ X41 @ X42 )
        = ( k4_xboole_0 @ X41 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('25',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ( X11 = X12 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k3_subset_1 @ X45 @ ( k3_subset_1 @ X45 @ X44 ) )
        = X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_subset_1 @ X1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X59: $i] :
      ( ( ( k2_struct_0 @ X59 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X59 ) @ ( k1_struct_0 @ X59 ) ) )
      | ~ ( l1_struct_0 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('35',plain,(
    ! [X58: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X58 ) )
      | ~ ( l1_struct_0 @ X58 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

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

thf('37',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('40',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('47',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ( v4_pre_topc @ X55 @ X56 )
      | ~ ( v1_xboole_0 @ X55 )
      | ~ ( l1_pre_topc @ X56 )
      | ~ ( v2_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
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

thf('54',plain,(
    ! [X60: $i,X61: $i] :
      ( ~ ( m1_subset_1 @ X60 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X61 ) ) )
      | ~ ( v4_pre_topc @ X60 @ X61 )
      | ( ( k2_pre_topc @ X61 @ X60 )
        = X60 )
      | ~ ( l1_pre_topc @ X61 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','60'])).

thf('62',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X43 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X62: $i,X63: $i] :
      ( ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X63 ) ) )
      | ( ( k1_tops_1 @ X63 @ X62 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X63 ) @ ( k2_pre_topc @ X63 @ ( k3_subset_1 @ ( u1_struct_0 @ X63 ) @ X62 ) ) ) )
      | ~ ( l1_pre_topc @ X63 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','15'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','14'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['38','71'])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('74',plain,(
    ! [X57: $i] :
      ( ( l1_struct_0 @ X57 )
      | ~ ( l1_pre_topc @ X57 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['37','76'])).

thf('78',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','77'])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('80',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(simplify,[status(thm)],['80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Qj7gWg5bjt
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:42:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 893 iterations in 0.330s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.59/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.59/0.79  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.59/0.79  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.59/0.79  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.59/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.79  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.59/0.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.79  thf(t4_subset_1, axiom,
% 0.59/0.79    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X46 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 0.59/0.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.79  thf(involutiveness_k3_subset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.79       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X44 : $i, X45 : $i]:
% 0.59/0.79         (((k3_subset_1 @ X45 @ (k3_subset_1 @ X45 @ X44)) = (X44))
% 0.59/0.79          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 0.59/0.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X46 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 0.59/0.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.79  thf(d5_subset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.79       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (![X41 : $i, X42 : $i]:
% 0.59/0.79         (((k3_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))
% 0.59/0.79          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.79  thf('5', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.79  thf(t2_boole, axiom,
% 0.59/0.79    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X9 : $i]: ((k3_xboole_0 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('cnf', [status(esa)], [t2_boole])).
% 0.59/0.79  thf(t12_setfam_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (![X47 : $i, X48 : $i]:
% 0.59/0.79         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (![X9 : $i]:
% 0.59/0.79         ((k1_setfam_1 @ (k2_tarski @ X9 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['6', '7'])).
% 0.59/0.79  thf(t100_xboole_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X7 @ X8)
% 0.59/0.79           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X47 : $i, X48 : $i]:
% 0.59/0.79         ((k1_setfam_1 @ (k2_tarski @ X47 @ X48)) = (k3_xboole_0 @ X47 @ X48))),
% 0.59/0.79      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X7 : $i, X8 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X7 @ X8)
% 0.59/0.79           = (k5_xboole_0 @ X7 @ (k1_setfam_1 @ (k2_tarski @ X7 @ X8))))),
% 0.59/0.79      inference('demod', [status(thm)], ['9', '10'])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['8', '11'])).
% 0.59/0.79  thf(t5_boole, axiom,
% 0.59/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.59/0.79  thf('13', plain, (![X10 : $i]: ((k5_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.59/0.79      inference('cnf', [status(esa)], [t5_boole])).
% 0.59/0.79  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('15', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['5', '14'])).
% 0.59/0.79  thf('16', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['2', '15'])).
% 0.59/0.79  thf(dt_k2_subset_1, axiom,
% 0.59/0.79    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X43 : $i]: (m1_subset_1 @ (k2_subset_1 @ X43) @ (k1_zfmisc_1 @ X43))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.59/0.79  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.59/0.79  thf('18', plain, (![X40 : $i]: ((k2_subset_1 @ X40) = (X40))),
% 0.59/0.79      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.59/0.79  thf('19', plain, (![X43 : $i]: (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X43))),
% 0.59/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X41 : $i, X42 : $i]:
% 0.59/0.79         (((k3_subset_1 @ X41 @ X42) = (k4_xboole_0 @ X41 @ X42))
% 0.59/0.79          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X41)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.79  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['16', '21'])).
% 0.59/0.79  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.79  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('24', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['22', '23'])).
% 0.59/0.79  thf(t8_boole, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X11) | ~ (v1_xboole_0 @ X12) | ((X11) = (X12)))),
% 0.59/0.79      inference('cnf', [status(esa)], [t8_boole])).
% 0.59/0.79  thf('26', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k4_xboole_0 @ X0 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('27', plain, (![X43 : $i]: (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X43))),
% 0.59/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (![X44 : $i, X45 : $i]:
% 0.59/0.79         (((k3_subset_1 @ X45 @ (k3_subset_1 @ X45 @ X44)) = (X44))
% 0.59/0.79          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 0.59/0.79      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.59/0.79  thf('29', plain,
% 0.59/0.79      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['27', '28'])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.79  thf('31', plain,
% 0.59/0.79      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k3_subset_1 @ X1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['26', '31'])).
% 0.59/0.79  thf(t27_pre_topc, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( l1_struct_0 @ A ) =>
% 0.59/0.79       ( ( k2_struct_0 @ A ) =
% 0.59/0.79         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      (![X59 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X59)
% 0.59/0.79            = (k3_subset_1 @ (u1_struct_0 @ X59) @ (k1_struct_0 @ X59)))
% 0.59/0.79          | ~ (l1_struct_0 @ X59))),
% 0.59/0.79      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.59/0.79          | ~ (v1_xboole_0 @ (k1_struct_0 @ X0))
% 0.59/0.79          | ~ (l1_struct_0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['32', '33'])).
% 0.59/0.79  thf(fc3_struct_0, axiom,
% 0.59/0.79    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      (![X58 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (k1_struct_0 @ X58)) | ~ (l1_struct_0 @ X58))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.59/0.79      inference('clc', [status(thm)], ['34', '35'])).
% 0.59/0.79  thf(t43_tops_1, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.59/0.79      inference('clc', [status(thm)], ['34', '35'])).
% 0.59/0.79  thf('39', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k4_xboole_0 @ X0 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.79      inference('sup-', [status(thm)], ['24', '25'])).
% 0.59/0.79  thf('40', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['16', '21'])).
% 0.59/0.79  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(d3_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (![X4 : $i, X6 : $i]:
% 0.59/0.79         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.79  thf(d1_xboole_0, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['42', '43'])).
% 0.59/0.79  thf(t3_subset, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.79  thf('45', plain,
% 0.59/0.79      (![X49 : $i, X51 : $i]:
% 0.59/0.79         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 0.59/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['44', '45'])).
% 0.59/0.79  thf(cc2_pre_topc, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X55 : $i, X56 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 0.59/0.79          | (v4_pre_topc @ X55 @ X56)
% 0.59/0.79          | ~ (v1_xboole_0 @ X55)
% 0.59/0.79          | ~ (l1_pre_topc @ X56)
% 0.59/0.79          | ~ (v2_pre_topc @ X56))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.59/0.79  thf('48', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X1)
% 0.59/0.79          | ~ (v2_pre_topc @ X0)
% 0.59/0.79          | ~ (l1_pre_topc @ X0)
% 0.59/0.79          | ~ (v1_xboole_0 @ X1)
% 0.59/0.79          | (v4_pre_topc @ X1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.79  thf('49', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         ((v4_pre_topc @ X1 @ X0)
% 0.59/0.79          | ~ (l1_pre_topc @ X0)
% 0.59/0.79          | ~ (v2_pre_topc @ X0)
% 0.59/0.79          | ~ (v1_xboole_0 @ X1))),
% 0.59/0.79      inference('simplify', [status(thm)], ['48'])).
% 0.59/0.79  thf('50', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ X0)
% 0.59/0.79          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.79          | (v4_pre_topc @ X0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['41', '49'])).
% 0.59/0.79  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['50', '51'])).
% 0.59/0.79  thf('53', plain,
% 0.59/0.79      (![X46 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 0.59/0.79      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.79  thf(t52_pre_topc, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( l1_pre_topc @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.59/0.79             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.59/0.79               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      (![X60 : $i, X61 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X60 @ (k1_zfmisc_1 @ (u1_struct_0 @ X61)))
% 0.59/0.79          | ~ (v4_pre_topc @ X60 @ X61)
% 0.59/0.79          | ((k2_pre_topc @ X61 @ X60) = (X60))
% 0.59/0.79          | ~ (l1_pre_topc @ X61))),
% 0.59/0.79      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (l1_pre_topc @ X0)
% 0.59/0.79          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.79          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['53', '54'])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.79        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['52', '55'])).
% 0.59/0.79  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('59', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['40', '59'])).
% 0.59/0.79  thf('61', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k2_pre_topc @ sk_A @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['39', '60'])).
% 0.59/0.79  thf('62', plain, (![X43 : $i]: (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X43))),
% 0.59/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf(d1_tops_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( l1_pre_topc @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79           ( ( k1_tops_1 @ A @ B ) =
% 0.59/0.79             ( k3_subset_1 @
% 0.59/0.79               ( u1_struct_0 @ A ) @ 
% 0.59/0.79               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.59/0.79  thf('63', plain,
% 0.59/0.79      (![X62 : $i, X63 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (u1_struct_0 @ X63)))
% 0.59/0.79          | ((k1_tops_1 @ X63 @ X62)
% 0.59/0.79              = (k3_subset_1 @ (u1_struct_0 @ X63) @ 
% 0.59/0.79                 (k2_pre_topc @ X63 @ (k3_subset_1 @ (u1_struct_0 @ X63) @ X62))))
% 0.59/0.79          | ~ (l1_pre_topc @ X63))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.59/0.79  thf('64', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (l1_pre_topc @ X0)
% 0.59/0.79          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.59/0.79              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.59/0.79                 (k2_pre_topc @ X0 @ 
% 0.59/0.79                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['62', '63'])).
% 0.59/0.79  thf('65', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.59/0.79      inference('demod', [status(thm)], ['2', '15'])).
% 0.59/0.79  thf('66', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (l1_pre_topc @ X0)
% 0.59/0.79          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.59/0.79              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.59/0.79                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.59/0.79      inference('demod', [status(thm)], ['64', '65'])).
% 0.59/0.79  thf('67', plain,
% 0.59/0.79      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.59/0.79          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.59/0.79        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.79        | ~ (l1_pre_topc @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['61', '66'])).
% 0.59/0.79  thf('68', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.59/0.79      inference('demod', [status(thm)], ['5', '14'])).
% 0.59/0.79  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.79      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.79  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('71', plain,
% 0.59/0.79      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.59/0.79  thf('72', plain,
% 0.59/0.79      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['38', '71'])).
% 0.59/0.79  thf('73', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(dt_l1_pre_topc, axiom,
% 0.59/0.79    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.79  thf('74', plain,
% 0.59/0.79      (![X57 : $i]: ((l1_struct_0 @ X57) | ~ (l1_pre_topc @ X57))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.59/0.79  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('sup-', [status(thm)], ['73', '74'])).
% 0.59/0.79  thf('76', plain,
% 0.59/0.79      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['72', '75'])).
% 0.59/0.79  thf('77', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['37', '76'])).
% 0.59/0.79  thf('78', plain,
% 0.59/0.79      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['36', '77'])).
% 0.59/0.79  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('sup-', [status(thm)], ['73', '74'])).
% 0.59/0.79  thf('80', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['78', '79'])).
% 0.59/0.79  thf('81', plain, ($false), inference('simplify', [status(thm)], ['80'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
