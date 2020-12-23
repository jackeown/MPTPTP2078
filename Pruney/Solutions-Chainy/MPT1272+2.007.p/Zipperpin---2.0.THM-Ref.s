%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SdAoItBrXr

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:29 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 643 expanded)
%              Number of leaves         :   35 ( 212 expanded)
%              Depth                    :   18
%              Number of atoms          : 1605 (5743 expanded)
%              Number of equality atoms :   81 ( 286 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_tops_1_type,type,(
    v3_tops_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t91_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
           => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_tops_1 @ B @ A )
             => ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t91_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('1',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X46 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('13',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k1_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','11','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('34',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','45'])).

thf('47',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('48',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X7 ) @ ( k4_xboole_0 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k4_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','56'])).

thf('58',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','57'])).

thf('59',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['19','57'])).

thf('64',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X27 @ ( k3_subset_1 @ X27 @ X26 ) )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('70',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('73',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('75',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(t84_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( ( k1_tops_1 @ A @ B )
              = k1_xboole_0 ) ) ) ) )).

thf('77',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k1_tops_1 @ X51 @ X50 )
       != k1_xboole_0 )
      | ( v2_tops_1 @ X50 @ X51 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('81',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
    | ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('84',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X42 ) ) )
      | ~ ( v2_tops_1 @ X41 @ X42 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X42 ) @ X41 ) @ X42 )
      | ~ ( l1_pre_topc @ X42 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('85',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('88',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86','87'])).

thf('89',plain,(
    ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('91',plain,(
    ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v2_tops_1 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['88','91'])).

thf('93',plain,(
    ( k1_tops_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['82','92'])).

thf('94',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['64','93'])).

thf('95',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( l1_pre_topc @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X37 @ X38 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_tarski @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('103',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('105',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X34: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( r1_tarski @ X34 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('109',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('110',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( r1_tarski @ X47 @ X49 )
      | ( r1_tarski @ ( k1_tops_1 @ X48 @ X47 ) @ ( k1_tops_1 @ X48 @ X49 ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['100','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('116',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X46 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X46 @ X45 ) @ X45 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('119',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('120',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('122',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X32 @ X31 ) @ ( k3_subset_1 @ X32 @ X33 ) )
      | ( r1_tarski @ X33 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('128',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k3_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['71','72'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('131',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X40 ) ) )
      | ( ( k1_tops_1 @ X40 @ X39 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ ( k2_pre_topc @ X40 @ ( k3_subset_1 @ ( u1_struct_0 @ X40 ) @ X39 ) ) ) )
      | ~ ( l1_pre_topc @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['129','134'])).

thf('136',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('137',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136','137'])).

thf('139',plain,
    ( ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','138'])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['117','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('144',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('146',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ~ ( v2_tops_1 @ X50 @ X51 )
      | ( ( k1_tops_1 @ X51 @ X50 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[t84_tops_1])).

thf('147',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tops_1 @ B @ A )
          <=> ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) )).

thf('150',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ~ ( v3_tops_1 @ X43 @ X44 )
      | ( v2_tops_1 @ ( k2_pre_topc @ X44 @ X43 ) @ X44 )
      | ~ ( l1_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[d5_tops_1])).

thf('151',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tops_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v3_tops_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v2_tops_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_pre_topc @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['147','148','154'])).

thf('156',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['114','144','155'])).

thf('157',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['95','156'])).

thf('158',plain,(
    $false ),
    inference(demod,[status(thm)],['94','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SdAoItBrXr
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.19/2.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.19/2.44  % Solved by: fo/fo7.sh
% 2.19/2.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.19/2.44  % done 4458 iterations in 1.989s
% 2.19/2.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.19/2.44  % SZS output start Refutation
% 2.19/2.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.19/2.44  thf(v3_tops_1_type, type, v3_tops_1: $i > $i > $o).
% 2.19/2.44  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.19/2.44  thf(sk_A_type, type, sk_A: $i).
% 2.19/2.44  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 2.19/2.44  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 2.19/2.44  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.19/2.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.19/2.44  thf(sk_B_type, type, sk_B: $i).
% 2.19/2.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.19/2.44  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.19/2.44  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 2.19/2.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.19/2.44  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 2.19/2.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.19/2.44  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.19/2.44  thf(t91_tops_1, conjecture,
% 2.19/2.44    (![A:$i]:
% 2.19/2.44     ( ( l1_pre_topc @ A ) =>
% 2.19/2.44       ( ![B:$i]:
% 2.19/2.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.44           ( ( v3_tops_1 @ B @ A ) =>
% 2.19/2.44             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 2.19/2.44  thf(zf_stmt_0, negated_conjecture,
% 2.19/2.44    (~( ![A:$i]:
% 2.19/2.44        ( ( l1_pre_topc @ A ) =>
% 2.19/2.44          ( ![B:$i]:
% 2.19/2.44            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.44              ( ( v3_tops_1 @ B @ A ) =>
% 2.19/2.44                ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ) )),
% 2.19/2.44    inference('cnf.neg', [status(esa)], [t91_tops_1])).
% 2.19/2.44  thf('0', plain,
% 2.19/2.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf(t44_tops_1, axiom,
% 2.19/2.44    (![A:$i]:
% 2.19/2.44     ( ( l1_pre_topc @ A ) =>
% 2.19/2.44       ( ![B:$i]:
% 2.19/2.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.44           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 2.19/2.44  thf('1', plain,
% 2.19/2.44      (![X45 : $i, X46 : $i]:
% 2.19/2.44         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 2.19/2.44          | (r1_tarski @ (k1_tops_1 @ X46 @ X45) @ X45)
% 2.19/2.44          | ~ (l1_pre_topc @ X46))),
% 2.19/2.44      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.19/2.44  thf('2', plain,
% 2.19/2.44      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['0', '1'])).
% 2.19/2.44  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf('4', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)),
% 2.19/2.44      inference('demod', [status(thm)], ['2', '3'])).
% 2.19/2.44  thf(t3_subset, axiom,
% 2.19/2.44    (![A:$i,B:$i]:
% 2.19/2.44     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.19/2.44  thf('5', plain,
% 2.19/2.44      (![X34 : $i, X36 : $i]:
% 2.19/2.44         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 2.19/2.44      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.44  thf('6', plain,
% 2.19/2.44      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['4', '5'])).
% 2.19/2.44  thf(involutiveness_k3_subset_1, axiom,
% 2.19/2.44    (![A:$i,B:$i]:
% 2.19/2.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.19/2.44       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.19/2.44  thf('7', plain,
% 2.19/2.44      (![X26 : $i, X27 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 2.19/2.44          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 2.19/2.44      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.19/2.44  thf('8', plain,
% 2.19/2.44      (((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))
% 2.19/2.44         = (k1_tops_1 @ sk_A @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['6', '7'])).
% 2.19/2.44  thf('9', plain,
% 2.19/2.44      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_zfmisc_1 @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['4', '5'])).
% 2.19/2.44  thf(d5_subset_1, axiom,
% 2.19/2.44    (![A:$i,B:$i]:
% 2.19/2.44     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.19/2.44       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 2.19/2.44  thf('10', plain,
% 2.19/2.44      (![X19 : $i, X20 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 2.19/2.44          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 2.19/2.44      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.19/2.44  thf('11', plain,
% 2.19/2.44      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.19/2.44         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['9', '10'])).
% 2.19/2.44  thf(t36_xboole_1, axiom,
% 2.19/2.44    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.19/2.44  thf('12', plain,
% 2.19/2.44      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 2.19/2.44      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.19/2.44  thf('13', plain,
% 2.19/2.44      (![X34 : $i, X36 : $i]:
% 2.19/2.44         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 2.19/2.44      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.44  thf('14', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['12', '13'])).
% 2.19/2.44  thf('15', plain,
% 2.19/2.44      (![X19 : $i, X20 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 2.19/2.44          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 2.19/2.44      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.19/2.44  thf('16', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.44           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['14', '15'])).
% 2.19/2.44  thf(t48_xboole_1, axiom,
% 2.19/2.44    (![A:$i,B:$i]:
% 2.19/2.44     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.19/2.44  thf('17', plain,
% 2.19/2.44      (![X14 : $i, X15 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 2.19/2.44           = (k3_xboole_0 @ X14 @ X15))),
% 2.19/2.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.44  thf('18', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.44           = (k3_xboole_0 @ X0 @ X1))),
% 2.19/2.44      inference('demod', [status(thm)], ['16', '17'])).
% 2.19/2.44  thf('19', plain,
% 2.19/2.44      (((k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 2.19/2.44         = (k1_tops_1 @ sk_A @ sk_B))),
% 2.19/2.44      inference('demod', [status(thm)], ['8', '11', '18'])).
% 2.19/2.44  thf('20', plain,
% 2.19/2.44      (![X14 : $i, X15 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 2.19/2.44           = (k3_xboole_0 @ X14 @ X15))),
% 2.19/2.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.44  thf(t3_boole, axiom,
% 2.19/2.44    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 2.19/2.44  thf('21', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 2.19/2.44      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.44  thf('22', plain,
% 2.19/2.44      (![X14 : $i, X15 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 2.19/2.44           = (k3_xboole_0 @ X14 @ X15))),
% 2.19/2.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.44  thf('23', plain,
% 2.19/2.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.44  thf('24', plain,
% 2.19/2.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.44  thf('25', plain,
% 2.19/2.44      (![X14 : $i, X15 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 2.19/2.44           = (k3_xboole_0 @ X14 @ X15))),
% 2.19/2.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.44  thf('26', plain,
% 2.19/2.44      (![X0 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 2.19/2.44           = (k3_xboole_0 @ X0 @ X0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['24', '25'])).
% 2.19/2.44  thf(d10_xboole_0, axiom,
% 2.19/2.44    (![A:$i,B:$i]:
% 2.19/2.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.19/2.44  thf('27', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.19/2.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.19/2.44  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.19/2.44      inference('simplify', [status(thm)], ['27'])).
% 2.19/2.44  thf('29', plain,
% 2.19/2.44      (![X34 : $i, X36 : $i]:
% 2.19/2.44         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 2.19/2.44      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.44  thf('30', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['28', '29'])).
% 2.19/2.44  thf('31', plain,
% 2.19/2.44      (![X26 : $i, X27 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 2.19/2.44          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 2.19/2.44      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.19/2.44  thf('32', plain,
% 2.19/2.44      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ X0)) = (X0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['30', '31'])).
% 2.19/2.44  thf('33', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['28', '29'])).
% 2.19/2.44  thf('34', plain,
% 2.19/2.44      (![X19 : $i, X20 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 2.19/2.44          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 2.19/2.44      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.19/2.44  thf('35', plain,
% 2.19/2.44      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['33', '34'])).
% 2.19/2.44  thf('36', plain,
% 2.19/2.44      (![X0 : $i]: ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X0)) = (X0))),
% 2.19/2.44      inference('demod', [status(thm)], ['32', '35'])).
% 2.19/2.44  thf('37', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.44           = (k3_xboole_0 @ X0 @ X1))),
% 2.19/2.44      inference('demod', [status(thm)], ['16', '17'])).
% 2.19/2.44  thf('38', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 2.19/2.44      inference('demod', [status(thm)], ['36', '37'])).
% 2.19/2.44  thf('39', plain,
% 2.19/2.44      (![X0 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 2.19/2.44      inference('demod', [status(thm)], ['26', '38'])).
% 2.19/2.44  thf(t38_xboole_1, axiom,
% 2.19/2.44    (![A:$i,B:$i]:
% 2.19/2.44     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 2.19/2.44       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 2.19/2.44  thf('40', plain,
% 2.19/2.44      (![X11 : $i, X12 : $i]:
% 2.19/2.44         (((X11) = (k1_xboole_0))
% 2.19/2.44          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 2.19/2.44      inference('cnf', [status(esa)], [t38_xboole_1])).
% 2.19/2.44  thf('41', plain,
% 2.19/2.44      (![X0 : $i]:
% 2.19/2.44         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X0)
% 2.19/2.44          | ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['39', '40'])).
% 2.19/2.44  thf('42', plain,
% 2.19/2.44      (![X14 : $i, X15 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 2.19/2.44           = (k3_xboole_0 @ X14 @ X15))),
% 2.19/2.44      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.19/2.44  thf('43', plain,
% 2.19/2.44      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 2.19/2.44      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.19/2.44  thf('44', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.19/2.44      inference('sup+', [status(thm)], ['42', '43'])).
% 2.19/2.44  thf('45', plain,
% 2.19/2.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.19/2.44      inference('demod', [status(thm)], ['41', '44'])).
% 2.19/2.44  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 2.19/2.44      inference('demod', [status(thm)], ['23', '45'])).
% 2.19/2.44  thf('47', plain,
% 2.19/2.44      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 2.19/2.44      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.19/2.44  thf(t34_xboole_1, axiom,
% 2.19/2.44    (![A:$i,B:$i,C:$i]:
% 2.19/2.44     ( ( r1_tarski @ A @ B ) =>
% 2.19/2.44       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 2.19/2.44  thf('48', plain,
% 2.19/2.44      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.19/2.44         (~ (r1_tarski @ X6 @ X7)
% 2.19/2.44          | (r1_tarski @ (k4_xboole_0 @ X8 @ X7) @ (k4_xboole_0 @ X8 @ X6)))),
% 2.19/2.44      inference('cnf', [status(esa)], [t34_xboole_1])).
% 2.19/2.44  thf('49', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.44         (r1_tarski @ (k4_xboole_0 @ X2 @ X0) @ 
% 2.19/2.44          (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['47', '48'])).
% 2.19/2.44  thf('50', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) @ 
% 2.19/2.44          k1_xboole_0)),
% 2.19/2.44      inference('sup+', [status(thm)], ['46', '49'])).
% 2.19/2.44  thf('51', plain,
% 2.19/2.44      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['21', '22'])).
% 2.19/2.44  thf('52', plain,
% 2.19/2.44      (![X11 : $i, X12 : $i]:
% 2.19/2.44         (((X11) = (k1_xboole_0))
% 2.19/2.44          | ~ (r1_tarski @ X11 @ (k4_xboole_0 @ X12 @ X11)))),
% 2.19/2.44      inference('cnf', [status(esa)], [t38_xboole_1])).
% 2.19/2.44  thf('53', plain,
% 2.19/2.44      (![X0 : $i]:
% 2.19/2.44         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))
% 2.19/2.44          | ((X0) = (k1_xboole_0)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['51', '52'])).
% 2.19/2.44  thf('54', plain,
% 2.19/2.44      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 2.19/2.44      inference('demod', [status(thm)], ['41', '44'])).
% 2.19/2.44  thf('55', plain,
% 2.19/2.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.19/2.44      inference('demod', [status(thm)], ['53', '54'])).
% 2.19/2.44  thf('56', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['50', '55'])).
% 2.19/2.44  thf('57', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['20', '56'])).
% 2.19/2.44  thf('58', plain,
% 2.19/2.44      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['19', '57'])).
% 2.19/2.44  thf('59', plain,
% 2.19/2.44      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 2.19/2.44      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.19/2.44  thf('60', plain,
% 2.19/2.44      (![X0 : $i, X2 : $i]:
% 2.19/2.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.19/2.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.19/2.44  thf('61', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.44          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['59', '60'])).
% 2.19/2.44  thf('62', plain,
% 2.19/2.44      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 2.19/2.44        | ((k1_tops_1 @ sk_A @ sk_B)
% 2.19/2.44            = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['58', '61'])).
% 2.19/2.44  thf('63', plain,
% 2.19/2.44      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 2.19/2.44      inference('sup+', [status(thm)], ['19', '57'])).
% 2.19/2.44  thf('64', plain,
% 2.19/2.44      ((~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 2.19/2.44        | ((k1_tops_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 2.19/2.44      inference('demod', [status(thm)], ['62', '63'])).
% 2.19/2.44  thf('65', plain,
% 2.19/2.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf('66', plain,
% 2.19/2.44      (![X26 : $i, X27 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X27 @ (k3_subset_1 @ X27 @ X26)) = (X26))
% 2.19/2.44          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 2.19/2.44      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.19/2.44  thf('67', plain,
% 2.19/2.44      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.19/2.44         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['65', '66'])).
% 2.19/2.44  thf('68', plain,
% 2.19/2.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf('69', plain,
% 2.19/2.44      (![X19 : $i, X20 : $i]:
% 2.19/2.44         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 2.19/2.44          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 2.19/2.44      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.19/2.44  thf('70', plain,
% 2.19/2.44      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.19/2.44         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['68', '69'])).
% 2.19/2.44  thf('71', plain,
% 2.19/2.44      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.19/2.44         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.19/2.44      inference('demod', [status(thm)], ['67', '70'])).
% 2.19/2.44  thf('72', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.44           = (k3_xboole_0 @ X0 @ X1))),
% 2.19/2.44      inference('demod', [status(thm)], ['16', '17'])).
% 2.19/2.44  thf('73', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 2.19/2.44      inference('demod', [status(thm)], ['71', '72'])).
% 2.19/2.44  thf('74', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.19/2.44      inference('sup+', [status(thm)], ['42', '43'])).
% 2.19/2.44  thf('75', plain,
% 2.19/2.44      (![X34 : $i, X36 : $i]:
% 2.19/2.44         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 2.19/2.44      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.44  thf('76', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.19/2.44      inference('sup-', [status(thm)], ['74', '75'])).
% 2.19/2.44  thf(t84_tops_1, axiom,
% 2.19/2.44    (![A:$i]:
% 2.19/2.44     ( ( l1_pre_topc @ A ) =>
% 2.19/2.44       ( ![B:$i]:
% 2.19/2.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.44           ( ( v2_tops_1 @ B @ A ) <=>
% 2.19/2.44             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 2.19/2.44  thf('77', plain,
% 2.19/2.44      (![X50 : $i, X51 : $i]:
% 2.19/2.44         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 2.19/2.44          | ((k1_tops_1 @ X51 @ X50) != (k1_xboole_0))
% 2.19/2.44          | (v2_tops_1 @ X50 @ X51)
% 2.19/2.44          | ~ (l1_pre_topc @ X51))),
% 2.19/2.44      inference('cnf', [status(esa)], [t84_tops_1])).
% 2.19/2.44  thf('78', plain,
% 2.19/2.44      (![X0 : $i, X1 : $i]:
% 2.19/2.44         (~ (l1_pre_topc @ X0)
% 2.19/2.44          | (v2_tops_1 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0)
% 2.19/2.44          | ((k1_tops_1 @ X0 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 2.19/2.44              != (k1_xboole_0)))),
% 2.19/2.44      inference('sup-', [status(thm)], ['76', '77'])).
% 2.19/2.44  thf('79', plain,
% 2.19/2.44      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 2.19/2.44        | (v2_tops_1 @ (k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.19/2.44        | ~ (l1_pre_topc @ sk_A))),
% 2.19/2.44      inference('sup-', [status(thm)], ['73', '78'])).
% 2.19/2.44  thf('80', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 2.19/2.44      inference('demod', [status(thm)], ['71', '72'])).
% 2.19/2.44  thf('81', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf('82', plain,
% 2.19/2.44      ((((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))
% 2.19/2.44        | (v2_tops_1 @ sk_B @ sk_A))),
% 2.19/2.44      inference('demod', [status(thm)], ['79', '80', '81'])).
% 2.19/2.44  thf('83', plain,
% 2.19/2.44      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf(d4_tops_1, axiom,
% 2.19/2.44    (![A:$i]:
% 2.19/2.44     ( ( l1_pre_topc @ A ) =>
% 2.19/2.44       ( ![B:$i]:
% 2.19/2.44         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.44           ( ( v2_tops_1 @ B @ A ) <=>
% 2.19/2.44             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 2.19/2.44  thf('84', plain,
% 2.19/2.44      (![X41 : $i, X42 : $i]:
% 2.19/2.44         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (u1_struct_0 @ X42)))
% 2.19/2.44          | ~ (v2_tops_1 @ X41 @ X42)
% 2.19/2.44          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X42) @ X41) @ X42)
% 2.19/2.44          | ~ (l1_pre_topc @ X42))),
% 2.19/2.44      inference('cnf', [status(esa)], [d4_tops_1])).
% 2.19/2.44  thf('85', plain,
% 2.19/2.44      ((~ (l1_pre_topc @ sk_A)
% 2.19/2.44        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.19/2.44        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.19/2.44      inference('sup-', [status(thm)], ['83', '84'])).
% 2.19/2.44  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf('87', plain,
% 2.19/2.44      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.19/2.44         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['68', '69'])).
% 2.19/2.44  thf('88', plain,
% 2.19/2.44      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)
% 2.19/2.44        | ~ (v2_tops_1 @ sk_B @ sk_A))),
% 2.19/2.44      inference('demod', [status(thm)], ['85', '86', '87'])).
% 2.19/2.44  thf('89', plain,
% 2.19/2.44      (~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.19/2.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.44  thf('90', plain,
% 2.19/2.44      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.19/2.44         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.19/2.44      inference('sup-', [status(thm)], ['68', '69'])).
% 2.19/2.44  thf('91', plain,
% 2.19/2.44      (~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A)),
% 2.19/2.44      inference('demod', [status(thm)], ['89', '90'])).
% 2.19/2.44  thf('92', plain, (~ (v2_tops_1 @ sk_B @ sk_A)),
% 2.19/2.45      inference('clc', [status(thm)], ['88', '91'])).
% 2.19/2.45  thf('93', plain, (((k1_tops_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 2.19/2.45      inference('clc', [status(thm)], ['82', '92'])).
% 2.19/2.45  thf('94', plain, (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 2.19/2.45      inference('simplify_reflect-', [status(thm)], ['64', '93'])).
% 2.19/2.45  thf('95', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 2.19/2.45      inference('cnf', [status(esa)], [t3_boole])).
% 2.19/2.45  thf('96', plain,
% 2.19/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf(dt_k2_pre_topc, axiom,
% 2.19/2.45    (![A:$i,B:$i]:
% 2.19/2.45     ( ( ( l1_pre_topc @ A ) & 
% 2.19/2.45         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 2.19/2.45       ( m1_subset_1 @
% 2.19/2.45         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.19/2.45  thf('97', plain,
% 2.19/2.45      (![X37 : $i, X38 : $i]:
% 2.19/2.45         (~ (l1_pre_topc @ X37)
% 2.19/2.45          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 2.19/2.45          | (m1_subset_1 @ (k2_pre_topc @ X37 @ X38) @ 
% 2.19/2.45             (k1_zfmisc_1 @ (u1_struct_0 @ X37))))),
% 2.19/2.45      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 2.19/2.45  thf('98', plain,
% 2.19/2.45      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.19/2.45         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.19/2.45        | ~ (l1_pre_topc @ sk_A))),
% 2.19/2.45      inference('sup-', [status(thm)], ['96', '97'])).
% 2.19/2.45  thf('99', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('100', plain,
% 2.19/2.45      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.19/2.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('demod', [status(thm)], ['98', '99'])).
% 2.19/2.45  thf('101', plain,
% 2.19/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('102', plain,
% 2.19/2.45      (![X34 : $i, X35 : $i]:
% 2.19/2.45         ((r1_tarski @ X34 @ X35) | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 2.19/2.45      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.45  thf('103', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 2.19/2.45      inference('sup-', [status(thm)], ['101', '102'])).
% 2.19/2.45  thf('104', plain,
% 2.19/2.45      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 2.19/2.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.19/2.45  thf(t1_xboole_1, axiom,
% 2.19/2.45    (![A:$i,B:$i,C:$i]:
% 2.19/2.45     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.19/2.45       ( r1_tarski @ A @ C ) ))).
% 2.19/2.45  thf('105', plain,
% 2.19/2.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 2.19/2.45         (~ (r1_tarski @ X3 @ X4)
% 2.19/2.45          | ~ (r1_tarski @ X4 @ X5)
% 2.19/2.45          | (r1_tarski @ X3 @ X5))),
% 2.19/2.45      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.19/2.45  thf('106', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.45         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 2.19/2.45      inference('sup-', [status(thm)], ['104', '105'])).
% 2.19/2.45  thf('107', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 2.19/2.45      inference('sup-', [status(thm)], ['103', '106'])).
% 2.19/2.45  thf('108', plain,
% 2.19/2.45      (![X34 : $i, X36 : $i]:
% 2.19/2.45         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X36)) | ~ (r1_tarski @ X34 @ X36))),
% 2.19/2.45      inference('cnf', [status(esa)], [t3_subset])).
% 2.19/2.45  thf('109', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.19/2.45          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('sup-', [status(thm)], ['107', '108'])).
% 2.19/2.45  thf(t48_tops_1, axiom,
% 2.19/2.45    (![A:$i]:
% 2.19/2.45     ( ( l1_pre_topc @ A ) =>
% 2.19/2.45       ( ![B:$i]:
% 2.19/2.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.45           ( ![C:$i]:
% 2.19/2.45             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.45               ( ( r1_tarski @ B @ C ) =>
% 2.19/2.45                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 2.19/2.45  thf('110', plain,
% 2.19/2.45      (![X47 : $i, X48 : $i, X49 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 2.19/2.45          | ~ (r1_tarski @ X47 @ X49)
% 2.19/2.45          | (r1_tarski @ (k1_tops_1 @ X48 @ X47) @ (k1_tops_1 @ X48 @ X49))
% 2.19/2.45          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 2.19/2.45          | ~ (l1_pre_topc @ X48))),
% 2.19/2.45      inference('cnf', [status(esa)], [t48_tops_1])).
% 2.19/2.45  thf('111', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (~ (l1_pre_topc @ sk_A)
% 2.19/2.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.19/2.45          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.19/2.45             (k1_tops_1 @ sk_A @ X1))
% 2.19/2.45          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 2.19/2.45      inference('sup-', [status(thm)], ['109', '110'])).
% 2.19/2.45  thf('112', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('113', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.19/2.45          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.19/2.45             (k1_tops_1 @ sk_A @ X1))
% 2.19/2.45          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 2.19/2.45      inference('demod', [status(thm)], ['111', '112'])).
% 2.19/2.45  thf('114', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ 
% 2.19/2.45             (k2_pre_topc @ sk_A @ sk_B))
% 2.19/2.45          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.19/2.45             (k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B))))),
% 2.19/2.45      inference('sup-', [status(thm)], ['100', '113'])).
% 2.19/2.45  thf('115', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.19/2.45      inference('sup-', [status(thm)], ['12', '13'])).
% 2.19/2.45  thf('116', plain,
% 2.19/2.45      (![X45 : $i, X46 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (u1_struct_0 @ X46)))
% 2.19/2.45          | (r1_tarski @ (k1_tops_1 @ X46 @ X45) @ X45)
% 2.19/2.45          | ~ (l1_pre_topc @ X46))),
% 2.19/2.45      inference('cnf', [status(esa)], [t44_tops_1])).
% 2.19/2.45  thf('117', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (~ (l1_pre_topc @ X0)
% 2.19/2.45          | (r1_tarski @ 
% 2.19/2.45             (k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)) @ 
% 2.19/2.45             (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1)))),
% 2.19/2.45      inference('sup-', [status(thm)], ['115', '116'])).
% 2.19/2.45  thf('118', plain,
% 2.19/2.45      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.19/2.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('demod', [status(thm)], ['98', '99'])).
% 2.19/2.45  thf('119', plain,
% 2.19/2.45      (![X19 : $i, X20 : $i]:
% 2.19/2.45         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 2.19/2.45          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 2.19/2.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 2.19/2.45  thf('120', plain,
% 2.19/2.45      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 2.19/2.45         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('sup-', [status(thm)], ['118', '119'])).
% 2.19/2.45  thf('121', plain,
% 2.19/2.45      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 2.19/2.45         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 2.19/2.45      inference('sup-', [status(thm)], ['68', '69'])).
% 2.19/2.45  thf(t31_subset_1, axiom,
% 2.19/2.45    (![A:$i,B:$i]:
% 2.19/2.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.19/2.45       ( ![C:$i]:
% 2.19/2.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.19/2.45           ( ( r1_tarski @ B @ C ) <=>
% 2.19/2.45             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 2.19/2.45  thf('122', plain,
% 2.19/2.45      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32))
% 2.19/2.45          | ~ (r1_tarski @ (k3_subset_1 @ X32 @ X31) @ 
% 2.19/2.45               (k3_subset_1 @ X32 @ X33))
% 2.19/2.45          | (r1_tarski @ X33 @ X31)
% 2.19/2.45          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 2.19/2.45      inference('cnf', [status(esa)], [t31_subset_1])).
% 2.19/2.45  thf('123', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.19/2.45             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.19/2.45          | (r1_tarski @ sk_B @ X0)
% 2.19/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.19/2.45      inference('sup-', [status(thm)], ['121', '122'])).
% 2.19/2.45  thf('124', plain,
% 2.19/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('125', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.19/2.45             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45          | (r1_tarski @ sk_B @ X0)
% 2.19/2.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 2.19/2.45      inference('demod', [status(thm)], ['123', '124'])).
% 2.19/2.45  thf('126', plain,
% 2.19/2.45      ((~ (r1_tarski @ 
% 2.19/2.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 2.19/2.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45        | ~ (m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.19/2.45             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.19/2.45        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('sup-', [status(thm)], ['120', '125'])).
% 2.19/2.45  thf('127', plain,
% 2.19/2.45      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.19/2.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('demod', [status(thm)], ['98', '99'])).
% 2.19/2.45  thf('128', plain,
% 2.19/2.45      ((~ (r1_tarski @ 
% 2.19/2.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 2.19/2.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('demod', [status(thm)], ['126', '127'])).
% 2.19/2.45  thf('129', plain, (((k3_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) = (sk_B))),
% 2.19/2.45      inference('demod', [status(thm)], ['71', '72'])).
% 2.19/2.45  thf('130', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.19/2.45      inference('sup-', [status(thm)], ['12', '13'])).
% 2.19/2.45  thf(d1_tops_1, axiom,
% 2.19/2.45    (![A:$i]:
% 2.19/2.45     ( ( l1_pre_topc @ A ) =>
% 2.19/2.45       ( ![B:$i]:
% 2.19/2.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.45           ( ( k1_tops_1 @ A @ B ) =
% 2.19/2.45             ( k3_subset_1 @
% 2.19/2.45               ( u1_struct_0 @ A ) @ 
% 2.19/2.45               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 2.19/2.45  thf('131', plain,
% 2.19/2.45      (![X39 : $i, X40 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (u1_struct_0 @ X40)))
% 2.19/2.45          | ((k1_tops_1 @ X40 @ X39)
% 2.19/2.45              = (k3_subset_1 @ (u1_struct_0 @ X40) @ 
% 2.19/2.45                 (k2_pre_topc @ X40 @ (k3_subset_1 @ (u1_struct_0 @ X40) @ X39))))
% 2.19/2.45          | ~ (l1_pre_topc @ X40))),
% 2.19/2.45      inference('cnf', [status(esa)], [d1_tops_1])).
% 2.19/2.45  thf('132', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (~ (l1_pre_topc @ X0)
% 2.19/2.45          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 2.19/2.45              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.19/2.45                 (k2_pre_topc @ X0 @ 
% 2.19/2.45                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.19/2.45                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 2.19/2.45      inference('sup-', [status(thm)], ['130', '131'])).
% 2.19/2.45  thf('133', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 2.19/2.45           = (k3_xboole_0 @ X0 @ X1))),
% 2.19/2.45      inference('demod', [status(thm)], ['16', '17'])).
% 2.19/2.45  thf('134', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i]:
% 2.19/2.45         (~ (l1_pre_topc @ X0)
% 2.19/2.45          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 2.19/2.45              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 2.19/2.45                 (k2_pre_topc @ X0 @ (k3_xboole_0 @ (u1_struct_0 @ X0) @ X1)))))),
% 2.19/2.45      inference('demod', [status(thm)], ['132', '133'])).
% 2.19/2.45  thf('135', plain,
% 2.19/2.45      ((((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))
% 2.19/2.45        | ~ (l1_pre_topc @ sk_A))),
% 2.19/2.45      inference('sup+', [status(thm)], ['129', '134'])).
% 2.19/2.45  thf('136', plain,
% 2.19/2.45      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B))
% 2.19/2.45         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('sup-', [status(thm)], ['118', '119'])).
% 2.19/2.45  thf('137', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('138', plain,
% 2.19/2.45      (((k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('demod', [status(thm)], ['135', '136', '137'])).
% 2.19/2.45  thf('139', plain,
% 2.19/2.45      ((~ (r1_tarski @ 
% 2.19/2.45           (k1_tops_1 @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 2.19/2.45           (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.19/2.45        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('demod', [status(thm)], ['128', '138'])).
% 2.19/2.45  thf('140', plain,
% 2.19/2.45      ((~ (l1_pre_topc @ sk_A)
% 2.19/2.45        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 2.19/2.45      inference('sup-', [status(thm)], ['117', '139'])).
% 2.19/2.45  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('142', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 2.19/2.45      inference('demod', [status(thm)], ['140', '141'])).
% 2.19/2.45  thf('143', plain,
% 2.19/2.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.19/2.45         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 2.19/2.45      inference('sup-', [status(thm)], ['104', '105'])).
% 2.19/2.45  thf('144', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (k2_pre_topc @ sk_A @ sk_B))),
% 2.19/2.45      inference('sup-', [status(thm)], ['142', '143'])).
% 2.19/2.45  thf('145', plain,
% 2.19/2.45      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 2.19/2.45        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('demod', [status(thm)], ['98', '99'])).
% 2.19/2.45  thf('146', plain,
% 2.19/2.45      (![X50 : $i, X51 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 2.19/2.45          | ~ (v2_tops_1 @ X50 @ X51)
% 2.19/2.45          | ((k1_tops_1 @ X51 @ X50) = (k1_xboole_0))
% 2.19/2.45          | ~ (l1_pre_topc @ X51))),
% 2.19/2.45      inference('cnf', [status(esa)], [t84_tops_1])).
% 2.19/2.45  thf('147', plain,
% 2.19/2.45      ((~ (l1_pre_topc @ sk_A)
% 2.19/2.45        | ((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))
% 2.19/2.45        | ~ (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 2.19/2.45      inference('sup-', [status(thm)], ['145', '146'])).
% 2.19/2.45  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('149', plain,
% 2.19/2.45      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf(d5_tops_1, axiom,
% 2.19/2.45    (![A:$i]:
% 2.19/2.45     ( ( l1_pre_topc @ A ) =>
% 2.19/2.45       ( ![B:$i]:
% 2.19/2.45         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.19/2.45           ( ( v3_tops_1 @ B @ A ) <=>
% 2.19/2.45             ( v2_tops_1 @ ( k2_pre_topc @ A @ B ) @ A ) ) ) ) ))).
% 2.19/2.45  thf('150', plain,
% 2.19/2.45      (![X43 : $i, X44 : $i]:
% 2.19/2.45         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 2.19/2.45          | ~ (v3_tops_1 @ X43 @ X44)
% 2.19/2.45          | (v2_tops_1 @ (k2_pre_topc @ X44 @ X43) @ X44)
% 2.19/2.45          | ~ (l1_pre_topc @ X44))),
% 2.19/2.45      inference('cnf', [status(esa)], [d5_tops_1])).
% 2.19/2.45  thf('151', plain,
% 2.19/2.45      ((~ (l1_pre_topc @ sk_A)
% 2.19/2.45        | (v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 2.19/2.45        | ~ (v3_tops_1 @ sk_B @ sk_A))),
% 2.19/2.45      inference('sup-', [status(thm)], ['149', '150'])).
% 2.19/2.45  thf('152', plain, ((l1_pre_topc @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('153', plain, ((v3_tops_1 @ sk_B @ sk_A)),
% 2.19/2.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.19/2.45  thf('154', plain, ((v2_tops_1 @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 2.19/2.45      inference('demod', [status(thm)], ['151', '152', '153'])).
% 2.19/2.45  thf('155', plain,
% 2.19/2.45      (((k1_tops_1 @ sk_A @ (k2_pre_topc @ sk_A @ sk_B)) = (k1_xboole_0))),
% 2.19/2.45      inference('demod', [status(thm)], ['147', '148', '154'])).
% 2.19/2.45  thf('156', plain,
% 2.19/2.45      (![X0 : $i]:
% 2.19/2.45         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 2.19/2.45          k1_xboole_0)),
% 2.19/2.45      inference('demod', [status(thm)], ['114', '144', '155'])).
% 2.19/2.45  thf('157', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)),
% 2.19/2.45      inference('sup+', [status(thm)], ['95', '156'])).
% 2.19/2.45  thf('158', plain, ($false), inference('demod', [status(thm)], ['94', '157'])).
% 2.19/2.45  
% 2.19/2.45  % SZS output end Refutation
% 2.19/2.45  
% 2.19/2.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
