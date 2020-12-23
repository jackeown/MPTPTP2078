%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eErgl2Nhhn

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:45 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  249 (3509 expanded)
%              Number of leaves         :   46 (1172 expanded)
%              Depth                    :   30
%              Number of atoms          : 2073 (26826 expanded)
%              Number of equality atoms :  159 (2670 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(t74_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X54 ) ) )
      | ( ( k1_tops_1 @ X54 @ X53 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X54 ) @ X53 @ ( k2_tops_1 @ X54 @ X53 ) ) )
      | ~ ( l1_pre_topc @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('36',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('39',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','43'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('61',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','63'])).

thf('65',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('68',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X23 @ X22 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X38 @ X39 ) )
      = ( k3_xboole_0 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('75',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k7_subset_1 @ X36 @ X35 @ X37 )
        = ( k4_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X1 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k7_subset_1 @ sk_B @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('83',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('86',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X52 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X52 @ X51 ) @ X51 )
      | ~ ( v4_pre_topc @ X51 @ X52 )
      | ~ ( l1_pre_topc @ X52 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('91',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_B @ X0 ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['81','93'])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('96',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) @ X0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('98',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = k1_xboole_0 )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('100',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('103',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('105',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('108',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['103','110'])).

thf('112',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('113',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('115',plain,
    ( ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['116'])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_subset_1 @ X26 @ X27 )
        = ( k4_xboole_0 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('120',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('122',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('123',plain,(
    ! [X28: $i,X29: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X28 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('124',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('125',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X50 ) ) )
      | ( ( k2_pre_topc @ X50 @ X49 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X50 ) @ X49 @ ( k2_tops_1 @ X50 @ X49 ) ) )
      | ~ ( l1_pre_topc @ X50 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('126',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k2_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('131',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['129','130'])).

thf('133',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['129','130'])).

thf('134',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['128','131','132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('136',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['83'])).

thf('137',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('139',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X2: $i] :
      ( ( k2_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k2_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['137','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('146',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ X0 @ sk_B ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['143','148'])).

thf('150',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('151',plain,
    ( ! [X0: $i] :
        ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('154',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('156',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('160',plain,(
    ! [X40: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X42 ) )
      | ~ ( r1_tarski @ X40 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('161',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['152','161'])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('163',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('164',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_subset_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ sk_B @ X1 )
        = ( k2_xboole_0 @ sk_B @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,
    ( ( ( k4_subset_1 @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['151','164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('168',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('169',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      | ~ ( r1_tarski @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('173',plain,
    ( ( k4_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('175',plain,
    ( ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('178',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('179',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( k2_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['175','176','177','178'])).

thf('180',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['137','142'])).

thf('181',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166','179','180'])).

thf('182',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['134','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('184',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( l1_pre_topc @ X45 )
      | ~ ( v2_pre_topc @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X45 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X45 @ X46 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('185',plain,
    ( ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v4_pre_topc @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['182','188'])).

thf('190',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['116'])).

thf('191',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['83'])).

thf('193',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['117','191','192'])).

thf('194',plain,
    ( ( k5_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['115','193'])).

thf('195',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['79','80','194'])).

thf('196',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['116'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('198',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['117','191'])).

thf('200',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['198','199'])).

thf('201',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['195','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eErgl2Nhhn
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:05:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.38/1.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.62  % Solved by: fo/fo7.sh
% 1.38/1.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.62  % done 3828 iterations in 1.160s
% 1.38/1.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.62  % SZS output start Refutation
% 1.38/1.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.38/1.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.38/1.62  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.38/1.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.38/1.62  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.38/1.62  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.38/1.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.38/1.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.38/1.62  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.38/1.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.38/1.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.38/1.62  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.38/1.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.38/1.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.38/1.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.38/1.62  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.38/1.62  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.38/1.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.62  thf(t77_tops_1, conjecture,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v4_pre_topc @ B @ A ) <=>
% 1.38/1.62             ( ( k2_tops_1 @ A @ B ) =
% 1.38/1.62               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.38/1.62  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.62    (~( ![A:$i]:
% 1.38/1.62        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.38/1.62          ( ![B:$i]:
% 1.38/1.62            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62              ( ( v4_pre_topc @ B @ A ) <=>
% 1.38/1.62                ( ( k2_tops_1 @ A @ B ) =
% 1.38/1.62                  ( k7_subset_1 @
% 1.38/1.62                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.38/1.62    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.38/1.62  thf('0', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(t74_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( k1_tops_1 @ A @ B ) =
% 1.38/1.62             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.38/1.62  thf('1', plain,
% 1.38/1.62      (![X53 : $i, X54 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (u1_struct_0 @ X54)))
% 1.38/1.62          | ((k1_tops_1 @ X54 @ X53)
% 1.38/1.62              = (k7_subset_1 @ (u1_struct_0 @ X54) @ X53 @ 
% 1.38/1.62                 (k2_tops_1 @ X54 @ X53)))
% 1.38/1.62          | ~ (l1_pre_topc @ X54))),
% 1.38/1.62      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.38/1.62  thf('2', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.38/1.62            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['0', '1'])).
% 1.38/1.62  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('4', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ sk_B)
% 1.38/1.62         = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('demod', [status(thm)], ['2', '3'])).
% 1.38/1.62  thf('5', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(redefinition_k7_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.38/1.62  thf('6', plain,
% 1.38/1.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.38/1.62          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.38/1.62  thf('7', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.38/1.62           = (k4_xboole_0 @ sk_B @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['5', '6'])).
% 1.38/1.62  thf('8', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ sk_B)
% 1.38/1.62         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('demod', [status(thm)], ['4', '7'])).
% 1.38/1.62  thf(t36_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.38/1.62  thf('9', plain,
% 1.38/1.62      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.38/1.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.38/1.62  thf(t43_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 1.38/1.62       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 1.38/1.62  thf('10', plain,
% 1.38/1.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.62         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.38/1.62          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.38/1.62  thf('11', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         (r1_tarski @ 
% 1.38/1.62          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X2) @ X1) @ 
% 1.38/1.62          X0)),
% 1.38/1.62      inference('sup-', [status(thm)], ['9', '10'])).
% 1.38/1.62  thf(commutativity_k2_tarski, axiom,
% 1.38/1.62    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.38/1.62  thf('12', plain,
% 1.38/1.62      (![X22 : $i, X23 : $i]:
% 1.38/1.62         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.38/1.62  thf(l51_zfmisc_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.38/1.62  thf('13', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.38/1.62  thf('14', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['12', '13'])).
% 1.38/1.62  thf('15', plain,
% 1.38/1.62      (![X24 : $i, X25 : $i]:
% 1.38/1.62         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 1.38/1.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.38/1.62  thf('16', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf(t1_boole, axiom,
% 1.38/1.62    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.38/1.62  thf('17', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_boole])).
% 1.38/1.62  thf('18', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['16', '17'])).
% 1.38/1.62  thf(t39_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.38/1.62  thf('19', plain,
% 1.38/1.62      (![X10 : $i, X11 : $i]:
% 1.38/1.62         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.38/1.62           = (k2_xboole_0 @ X10 @ X11))),
% 1.38/1.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.38/1.62  thf('20', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['18', '19'])).
% 1.38/1.62  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['16', '17'])).
% 1.38/1.62  thf('22', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '21'])).
% 1.38/1.62  thf('23', plain,
% 1.38/1.62      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.38/1.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.38/1.62  thf(t3_subset, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.38/1.62  thf('24', plain,
% 1.38/1.62      (![X40 : $i, X42 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('25', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['23', '24'])).
% 1.38/1.62  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['22', '25'])).
% 1.38/1.62  thf(d5_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.38/1.62  thf('27', plain,
% 1.38/1.62      (![X26 : $i, X27 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.38/1.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.38/1.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.38/1.62  thf('28', plain,
% 1.38/1.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['26', '27'])).
% 1.38/1.62  thf('29', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_boole])).
% 1.38/1.62  thf('30', plain,
% 1.38/1.62      (![X6 : $i, X7 : $i]: (r1_tarski @ (k4_xboole_0 @ X6 @ X7) @ X6)),
% 1.38/1.62      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.38/1.62  thf(t44_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 1.38/1.62       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.38/1.62  thf('31', plain,
% 1.38/1.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.38/1.62         ((r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 1.38/1.62          | ~ (r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17))),
% 1.38/1.62      inference('cnf', [status(esa)], [t44_xboole_1])).
% 1.38/1.62  thf('32', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.62  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.38/1.62      inference('sup+', [status(thm)], ['29', '32'])).
% 1.38/1.62  thf('34', plain,
% 1.38/1.62      (![X40 : $i, X42 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('35', plain,
% 1.38/1.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['33', '34'])).
% 1.38/1.62  thf(involutiveness_k3_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.38/1.62  thf('36', plain,
% 1.38/1.62      (![X30 : $i, X31 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 1.38/1.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('37', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['35', '36'])).
% 1.38/1.62  thf('38', plain,
% 1.38/1.62      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['33', '34'])).
% 1.38/1.62  thf('39', plain,
% 1.38/1.62      (![X26 : $i, X27 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.38/1.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.38/1.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.38/1.62  thf('40', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.62  thf('41', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '21'])).
% 1.38/1.62  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['40', '41'])).
% 1.38/1.62  thf('43', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['37', '42'])).
% 1.38/1.62  thf('44', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['28', '43'])).
% 1.38/1.62  thf(t48_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.38/1.62  thf('45', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.38/1.62           = (k3_xboole_0 @ X18 @ X19))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('46', plain,
% 1.38/1.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['44', '45'])).
% 1.38/1.62  thf('47', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '21'])).
% 1.38/1.62  thf('48', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['46', '47'])).
% 1.38/1.62  thf(t100_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.38/1.62  thf('49', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X0 @ X1)
% 1.38/1.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.38/1.62  thf('50', plain,
% 1.38/1.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['48', '49'])).
% 1.38/1.62  thf('51', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['28', '43'])).
% 1.38/1.62  thf('52', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['50', '51'])).
% 1.38/1.62  thf('53', plain,
% 1.38/1.62      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['26', '27'])).
% 1.38/1.62  thf(t38_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 1.38/1.62       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.38/1.62  thf('54', plain,
% 1.38/1.62      (![X8 : $i, X9 : $i]:
% 1.38/1.62         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.38/1.62  thf('55', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X0)) | ((X0) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['53', '54'])).
% 1.38/1.62  thf('56', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['37', '42'])).
% 1.38/1.62  thf('57', plain,
% 1.38/1.62      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['55', '56'])).
% 1.38/1.62  thf('58', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['52', '57'])).
% 1.38/1.62  thf('59', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ 
% 1.38/1.62           (k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) @ X2) @ 
% 1.38/1.62           X1) = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['11', '58'])).
% 1.38/1.62  thf('60', plain, (![X0 : $i]: ((k1_xboole_0) = (k5_xboole_0 @ X0 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['50', '51'])).
% 1.38/1.62  thf('61', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_boole])).
% 1.38/1.62  thf('62', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k2_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['60', '61'])).
% 1.38/1.62  thf('63', plain,
% 1.38/1.62      (![X1 : $i, X2 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['59', '62'])).
% 1.38/1.62  thf('64', plain,
% 1.38/1.62      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['8', '63'])).
% 1.38/1.62  thf('65', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.38/1.62           = (k3_xboole_0 @ X18 @ X19))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('66', plain,
% 1.38/1.62      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.38/1.62         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.38/1.62      inference('sup+', [status(thm)], ['64', '65'])).
% 1.38/1.62  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '21'])).
% 1.38/1.62  thf('68', plain,
% 1.38/1.62      (![X22 : $i, X23 : $i]:
% 1.38/1.62         ((k2_tarski @ X23 @ X22) = (k2_tarski @ X22 @ X23))),
% 1.38/1.62      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.38/1.62  thf(t12_setfam_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.38/1.62  thf('69', plain,
% 1.38/1.62      (![X38 : $i, X39 : $i]:
% 1.38/1.62         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 1.38/1.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.38/1.62  thf('70', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['68', '69'])).
% 1.38/1.62  thf('71', plain,
% 1.38/1.62      (![X38 : $i, X39 : $i]:
% 1.38/1.62         ((k1_setfam_1 @ (k2_tarski @ X38 @ X39)) = (k3_xboole_0 @ X38 @ X39))),
% 1.38/1.62      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.38/1.62  thf('72', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['70', '71'])).
% 1.38/1.62  thf('73', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ sk_B)
% 1.38/1.62         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('demod', [status(thm)], ['66', '67', '72'])).
% 1.38/1.62  thf('74', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['22', '25'])).
% 1.38/1.62  thf('75', plain,
% 1.38/1.62      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 1.38/1.62          | ((k7_subset_1 @ X36 @ X35 @ X37) = (k4_xboole_0 @ X35 @ X37)))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.38/1.62  thf('76', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['74', '75'])).
% 1.38/1.62  thf('77', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X0 @ X1)
% 1.38/1.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.38/1.62  thf('78', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k7_subset_1 @ X1 @ X1 @ X0)
% 1.38/1.62           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['76', '77'])).
% 1.38/1.62  thf('79', plain,
% 1.38/1.62      (((k7_subset_1 @ sk_B @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.38/1.62         = (k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['73', '78'])).
% 1.38/1.62  thf('80', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup-', [status(thm)], ['74', '75'])).
% 1.38/1.62  thf('81', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('82', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.62  thf('83', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62             (k1_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('84', plain,
% 1.38/1.62      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('split', [status(esa)], ['83'])).
% 1.38/1.62  thf('85', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(t69_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( v4_pre_topc @ B @ A ) =>
% 1.38/1.62             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.38/1.62  thf('86', plain,
% 1.38/1.62      (![X51 : $i, X52 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (u1_struct_0 @ X52)))
% 1.38/1.62          | (r1_tarski @ (k2_tops_1 @ X52 @ X51) @ X51)
% 1.38/1.62          | ~ (v4_pre_topc @ X51 @ X52)
% 1.38/1.62          | ~ (l1_pre_topc @ X52))),
% 1.38/1.62      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.38/1.62  thf('87', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.38/1.62        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['85', '86'])).
% 1.38/1.62  thf('88', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('89', plain,
% 1.38/1.62      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.38/1.62        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['87', '88'])).
% 1.38/1.62  thf('90', plain,
% 1.38/1.62      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['84', '89'])).
% 1.38/1.62  thf(t1_xboole_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.38/1.62       ( r1_tarski @ A @ C ) ))).
% 1.38/1.62  thf('91', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X3 @ X4)
% 1.38/1.62          | ~ (r1_tarski @ X4 @ X5)
% 1.38/1.62          | (r1_tarski @ X3 @ X5))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.62  thf('92', plain,
% 1.38/1.62      ((![X0 : $i]:
% 1.38/1.62          ((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ X0)
% 1.38/1.62           | ~ (r1_tarski @ sk_B @ X0)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['90', '91'])).
% 1.38/1.62  thf('93', plain,
% 1.38/1.62      ((![X0 : $i]:
% 1.38/1.62          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['82', '92'])).
% 1.38/1.62  thf('94', plain,
% 1.38/1.62      ((![X0 : $i]:
% 1.38/1.62          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ sk_B @ X0)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['81', '93'])).
% 1.38/1.62  thf('95', plain,
% 1.38/1.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.62         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.38/1.62          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.38/1.62  thf('96', plain,
% 1.38/1.62      ((![X0 : $i]:
% 1.38/1.62          (r1_tarski @ (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) @ X0))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['94', '95'])).
% 1.38/1.62  thf('97', plain,
% 1.38/1.62      (![X8 : $i, X9 : $i]:
% 1.38/1.62         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.38/1.62  thf('98', plain,
% 1.38/1.62      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['96', '97'])).
% 1.38/1.62  thf('99', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.38/1.62           = (k3_xboole_0 @ X18 @ X19))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('100', plain,
% 1.38/1.62      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.38/1.62          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['98', '99'])).
% 1.38/1.62  thf('101', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['20', '21'])).
% 1.38/1.62  thf('102', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['70', '71'])).
% 1.38/1.62  thf('103', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.38/1.62  thf('104', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X0 @ X1)
% 1.38/1.62           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.38/1.62  thf('105', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.38/1.62           = (k3_xboole_0 @ X18 @ X19))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('106', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 1.38/1.62           = (k3_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['104', '105'])).
% 1.38/1.62  thf('107', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.38/1.62           = (k3_xboole_0 @ X18 @ X19))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('108', plain,
% 1.38/1.62      (![X18 : $i, X19 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 1.38/1.62           = (k3_xboole_0 @ X18 @ X19))),
% 1.38/1.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.38/1.62  thf('109', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.62           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['107', '108'])).
% 1.38/1.62  thf('110', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.38/1.62           = (k3_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('demod', [status(thm)], ['106', '109'])).
% 1.38/1.62  thf('111', plain,
% 1.38/1.62      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['103', '110'])).
% 1.38/1.62  thf('112', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['100', '101', '102'])).
% 1.38/1.62  thf('113', plain,
% 1.38/1.62      ((((k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['111', '112'])).
% 1.38/1.62  thf('114', plain,
% 1.38/1.62      (((k1_tops_1 @ sk_A @ sk_B)
% 1.38/1.62         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('demod', [status(thm)], ['4', '7'])).
% 1.38/1.62  thf('115', plain,
% 1.38/1.62      ((((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.38/1.62          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['113', '114'])).
% 1.38/1.62  thf('116', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62              (k1_tops_1 @ sk_A @ sk_B)))
% 1.38/1.62        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('117', plain,
% 1.38/1.62      (~
% 1.38/1.62       (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.38/1.62       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.38/1.62      inference('split', [status(esa)], ['116'])).
% 1.38/1.62  thf('118', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('119', plain,
% 1.38/1.62      (![X26 : $i, X27 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X26 @ X27) = (k4_xboole_0 @ X26 @ X27))
% 1.38/1.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X26)))),
% 1.38/1.62      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.38/1.62  thf('120', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)
% 1.38/1.62         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['118', '119'])).
% 1.38/1.62  thf('121', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['23', '24'])).
% 1.38/1.62  thf('122', plain,
% 1.38/1.62      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['120', '121'])).
% 1.38/1.62  thf(dt_k3_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.38/1.62       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.38/1.62  thf('123', plain,
% 1.38/1.62      (![X28 : $i, X29 : $i]:
% 1.38/1.62         ((m1_subset_1 @ (k3_subset_1 @ X28 @ X29) @ (k1_zfmisc_1 @ X28))
% 1.38/1.62          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 1.38/1.62      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 1.38/1.62  thf('124', plain,
% 1.38/1.62      ((m1_subset_1 @ 
% 1.38/1.62        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.38/1.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['122', '123'])).
% 1.38/1.62  thf(t65_tops_1, axiom,
% 1.38/1.62    (![A:$i]:
% 1.38/1.62     ( ( l1_pre_topc @ A ) =>
% 1.38/1.62       ( ![B:$i]:
% 1.38/1.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.38/1.62           ( ( k2_pre_topc @ A @ B ) =
% 1.38/1.62             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.38/1.62  thf('125', plain,
% 1.38/1.62      (![X49 : $i, X50 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X50)))
% 1.38/1.62          | ((k2_pre_topc @ X50 @ X49)
% 1.38/1.62              = (k4_subset_1 @ (u1_struct_0 @ X50) @ X49 @ 
% 1.38/1.62                 (k2_tops_1 @ X50 @ X49)))
% 1.38/1.62          | ~ (l1_pre_topc @ X50))),
% 1.38/1.62      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.38/1.62  thf('126', plain,
% 1.38/1.62      ((~ (l1_pre_topc @ sk_A)
% 1.38/1.62        | ((k2_pre_topc @ sk_A @ 
% 1.38/1.62            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.38/1.62            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.38/1.62               (k2_tops_1 @ sk_A @ 
% 1.38/1.62                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['124', '125'])).
% 1.38/1.62  thf('127', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('128', plain,
% 1.38/1.62      (((k2_pre_topc @ sk_A @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 1.38/1.62         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 1.38/1.62            (k2_tops_1 @ sk_A @ 
% 1.38/1.62             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 1.38/1.62      inference('demod', [status(thm)], ['126', '127'])).
% 1.38/1.62  thf('129', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('130', plain,
% 1.38/1.62      (![X30 : $i, X31 : $i]:
% 1.38/1.62         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 1.38/1.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 1.38/1.62      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.38/1.62  thf('131', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('132', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('133', plain,
% 1.38/1.62      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.38/1.62         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 1.38/1.62      inference('sup-', [status(thm)], ['129', '130'])).
% 1.38/1.62  thf('134', plain,
% 1.38/1.62      (((k2_pre_topc @ sk_A @ sk_B)
% 1.38/1.62         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('demod', [status(thm)], ['128', '131', '132', '133'])).
% 1.38/1.62  thf('135', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.38/1.62           = (k4_xboole_0 @ sk_B @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['5', '6'])).
% 1.38/1.62  thf('136', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62             (k1_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('split', [status(esa)], ['83'])).
% 1.38/1.62  thf('137', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup+', [status(thm)], ['135', '136'])).
% 1.38/1.62  thf('138', plain,
% 1.38/1.62      (![X1 : $i, X2 : $i]:
% 1.38/1.62         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X1) = (k1_xboole_0))),
% 1.38/1.62      inference('demod', [status(thm)], ['59', '62'])).
% 1.38/1.62  thf('139', plain,
% 1.38/1.62      (![X10 : $i, X11 : $i]:
% 1.38/1.62         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.38/1.62           = (k2_xboole_0 @ X10 @ X11))),
% 1.38/1.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.38/1.62  thf('140', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((k2_xboole_0 @ X1 @ k1_xboole_0)
% 1.38/1.62           = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['138', '139'])).
% 1.38/1.62  thf('141', plain, (![X2 : $i]: ((k2_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_boole])).
% 1.38/1.62  thf('142', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         ((X1) = (k2_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('demod', [status(thm)], ['140', '141'])).
% 1.38/1.62  thf('143', plain,
% 1.38/1.62      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup+', [status(thm)], ['137', '142'])).
% 1.38/1.62  thf('144', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.62  thf('145', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.62  thf('146', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X3 @ X4)
% 1.38/1.62          | ~ (r1_tarski @ X4 @ X5)
% 1.38/1.62          | (r1_tarski @ X3 @ X5))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.62  thf('147', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         ((r1_tarski @ X0 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 1.38/1.62      inference('sup-', [status(thm)], ['145', '146'])).
% 1.38/1.62  thf('148', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.62         (r1_tarski @ X0 @ (k2_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['144', '147'])).
% 1.38/1.62  thf('149', plain,
% 1.38/1.62      ((![X0 : $i]:
% 1.38/1.62          (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ (k2_xboole_0 @ X0 @ sk_B)))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup+', [status(thm)], ['143', '148'])).
% 1.38/1.62  thf('150', plain,
% 1.38/1.62      (![X40 : $i, X42 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('151', plain,
% 1.38/1.62      ((![X0 : $i]:
% 1.38/1.62          (m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.38/1.62           (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_B))))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['149', '150'])).
% 1.38/1.62  thf('152', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('153', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.62  thf('154', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('155', plain,
% 1.38/1.62      (![X40 : $i, X41 : $i]:
% 1.38/1.62         ((r1_tarski @ X40 @ X41) | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('156', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['154', '155'])).
% 1.38/1.62  thf('157', plain,
% 1.38/1.62      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.38/1.62         (~ (r1_tarski @ X3 @ X4)
% 1.38/1.62          | ~ (r1_tarski @ X4 @ X5)
% 1.38/1.62          | (r1_tarski @ X3 @ X5))),
% 1.38/1.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.38/1.62  thf('158', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ (u1_struct_0 @ sk_A) @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['156', '157'])).
% 1.38/1.62  thf('159', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['153', '158'])).
% 1.38/1.62  thf('160', plain,
% 1.38/1.62      (![X40 : $i, X42 : $i]:
% 1.38/1.62         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X42)) | ~ (r1_tarski @ X40 @ X42))),
% 1.38/1.62      inference('cnf', [status(esa)], [t3_subset])).
% 1.38/1.62  thf('161', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (m1_subset_1 @ sk_B @ 
% 1.38/1.62          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['159', '160'])).
% 1.38/1.62  thf('162', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (m1_subset_1 @ sk_B @ 
% 1.38/1.62          (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.38/1.62      inference('sup+', [status(thm)], ['152', '161'])).
% 1.38/1.62  thf(redefinition_k4_subset_1, axiom,
% 1.38/1.62    (![A:$i,B:$i,C:$i]:
% 1.38/1.62     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.38/1.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.38/1.62       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.38/1.62  thf('163', plain,
% 1.38/1.62      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.38/1.62         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.38/1.62          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 1.38/1.62          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 1.38/1.62      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.38/1.62  thf('164', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]:
% 1.38/1.62         (((k4_subset_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0) @ sk_B @ X1)
% 1.38/1.62            = (k2_xboole_0 @ sk_B @ X1))
% 1.38/1.62          | ~ (m1_subset_1 @ X1 @ 
% 1.38/1.62               (k1_zfmisc_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['162', '163'])).
% 1.38/1.62  thf('165', plain,
% 1.38/1.62      ((((k4_subset_1 @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_B @ 
% 1.38/1.62          (k2_tops_1 @ sk_A @ sk_B))
% 1.38/1.62          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['151', '164'])).
% 1.38/1.62  thf('166', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('167', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('168', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('sup-', [status(thm)], ['153', '158'])).
% 1.38/1.62  thf('169', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (r1_tarski @ sk_B @ (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['167', '168'])).
% 1.38/1.62  thf('170', plain,
% 1.38/1.62      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.38/1.62         ((r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 1.38/1.62          | ~ (r1_tarski @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t43_xboole_1])).
% 1.38/1.62  thf('171', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         (r1_tarski @ (k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) @ X0)),
% 1.38/1.62      inference('sup-', [status(thm)], ['169', '170'])).
% 1.38/1.62  thf('172', plain,
% 1.38/1.62      (![X8 : $i, X9 : $i]:
% 1.38/1.62         (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 1.38/1.62      inference('cnf', [status(esa)], [t38_xboole_1])).
% 1.38/1.62  thf('173', plain,
% 1.38/1.62      (((k4_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)) = (k1_xboole_0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['171', '172'])).
% 1.38/1.62  thf('174', plain,
% 1.38/1.62      (![X10 : $i, X11 : $i]:
% 1.38/1.62         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 1.38/1.62           = (k2_xboole_0 @ X10 @ X11))),
% 1.38/1.62      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.38/1.62  thf('175', plain,
% 1.38/1.62      (((k2_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 1.38/1.62         = (k2_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 1.38/1.62      inference('sup+', [status(thm)], ['173', '174'])).
% 1.38/1.62  thf('176', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('177', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.38/1.62      inference('sup+', [status(thm)], ['16', '17'])).
% 1.38/1.62  thf('178', plain,
% 1.38/1.62      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.38/1.62      inference('sup+', [status(thm)], ['14', '15'])).
% 1.38/1.62  thf('179', plain,
% 1.38/1.62      (((u1_struct_0 @ sk_A) = (k2_xboole_0 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('demod', [status(thm)], ['175', '176', '177', '178'])).
% 1.38/1.62  thf('180', plain,
% 1.38/1.62      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup+', [status(thm)], ['137', '142'])).
% 1.38/1.62  thf('181', plain,
% 1.38/1.62      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.38/1.62          = (sk_B)))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('demod', [status(thm)], ['165', '166', '179', '180'])).
% 1.38/1.62  thf('182', plain,
% 1.38/1.62      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup+', [status(thm)], ['134', '181'])).
% 1.38/1.62  thf('183', plain,
% 1.38/1.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf(fc1_tops_1, axiom,
% 1.38/1.62    (![A:$i,B:$i]:
% 1.38/1.62     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 1.38/1.62         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.38/1.62       ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ))).
% 1.38/1.62  thf('184', plain,
% 1.38/1.62      (![X45 : $i, X46 : $i]:
% 1.38/1.62         (~ (l1_pre_topc @ X45)
% 1.38/1.62          | ~ (v2_pre_topc @ X45)
% 1.38/1.62          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (u1_struct_0 @ X45)))
% 1.38/1.62          | (v4_pre_topc @ (k2_pre_topc @ X45 @ X46) @ X45))),
% 1.38/1.62      inference('cnf', [status(esa)], [fc1_tops_1])).
% 1.38/1.62  thf('185', plain,
% 1.38/1.62      (((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)
% 1.38/1.62        | ~ (v2_pre_topc @ sk_A)
% 1.38/1.62        | ~ (l1_pre_topc @ sk_A))),
% 1.38/1.62      inference('sup-', [status(thm)], ['183', '184'])).
% 1.38/1.62  thf('186', plain, ((v2_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('187', plain, ((l1_pre_topc @ sk_A)),
% 1.38/1.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.62  thf('188', plain, ((v4_pre_topc @ (k2_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 1.38/1.62      inference('demod', [status(thm)], ['185', '186', '187'])).
% 1.38/1.62  thf('189', plain,
% 1.38/1.62      (((v4_pre_topc @ sk_B @ sk_A))
% 1.38/1.62         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('sup+', [status(thm)], ['182', '188'])).
% 1.38/1.62  thf('190', plain,
% 1.38/1.62      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.38/1.62      inference('split', [status(esa)], ['116'])).
% 1.38/1.62  thf('191', plain,
% 1.38/1.62      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.38/1.62       ~
% 1.38/1.62       (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.38/1.62      inference('sup-', [status(thm)], ['189', '190'])).
% 1.38/1.62  thf('192', plain,
% 1.38/1.62      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.38/1.62       (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.38/1.62      inference('split', [status(esa)], ['83'])).
% 1.38/1.62  thf('193', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.38/1.62      inference('sat_resolution*', [status(thm)], ['117', '191', '192'])).
% 1.38/1.62  thf('194', plain,
% 1.38/1.62      (((k5_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.38/1.62         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('simpl_trail', [status(thm)], ['115', '193'])).
% 1.38/1.62  thf('195', plain,
% 1.38/1.62      (((k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.38/1.62         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.38/1.62      inference('demod', [status(thm)], ['79', '80', '194'])).
% 1.38/1.62  thf('196', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62              (k1_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= (~
% 1.38/1.62             (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('split', [status(esa)], ['116'])).
% 1.38/1.62  thf('197', plain,
% 1.38/1.62      (![X0 : $i]:
% 1.38/1.62         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.38/1.62           = (k4_xboole_0 @ sk_B @ X0))),
% 1.38/1.62      inference('sup-', [status(thm)], ['5', '6'])).
% 1.38/1.62  thf('198', plain,
% 1.38/1.62      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.38/1.62         <= (~
% 1.38/1.62             (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.38/1.62      inference('demod', [status(thm)], ['196', '197'])).
% 1.38/1.62  thf('199', plain,
% 1.38/1.62      (~
% 1.38/1.62       (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.38/1.62             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.38/1.62      inference('sat_resolution*', [status(thm)], ['117', '191'])).
% 1.38/1.62  thf('200', plain,
% 1.38/1.62      (((k2_tops_1 @ sk_A @ sk_B)
% 1.38/1.62         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.38/1.62      inference('simpl_trail', [status(thm)], ['198', '199'])).
% 1.38/1.62  thf('201', plain, ($false),
% 1.38/1.62      inference('simplify_reflect-', [status(thm)], ['195', '200'])).
% 1.38/1.62  
% 1.38/1.62  % SZS output end Refutation
% 1.38/1.62  
% 1.38/1.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
