%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z9Zpv0gGoa

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:51 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  181 ( 666 expanded)
%              Number of leaves         :   42 ( 221 expanded)
%              Depth                    :   16
%              Number of atoms          : 1594 (6878 expanded)
%              Number of equality atoms :  132 ( 538 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k2_tops_1_type,type,(
    k2_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X63: $i,X64: $i] :
      ( ~ ( m1_subset_1 @ X63 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X64 ) ) )
      | ( ( k1_tops_1 @ X64 @ X63 )
        = ( k7_subset_1 @ ( u1_struct_0 @ X64 ) @ X63 @ ( k2_tops_1 @ X64 @ X63 ) ) )
      | ~ ( l1_pre_topc @ X64 ) ) ),
    inference(cnf,[status(esa)],[t74_tops_1])).

thf('2',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) )
      | ( ( k7_subset_1 @ X41 @ X40 @ X42 )
        = ( k4_xboole_0 @ X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = sk_B ),
    inference('sup+',[status(thm)],['7','12'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X26 ) @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('15',plain,(
    ! [X23: $i] :
      ( ( k2_subset_1 @ X23 )
      = X23 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('16',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      = ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X46: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['13','37'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,
    ( ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('42',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','45','46'])).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('49',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','58'])).

thf('60',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
           => ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) )).

thf('63',plain,(
    ! [X61: $i,X62: $i] :
      ( ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X62 ) ) )
      | ( r1_tarski @ ( k2_tops_1 @ X62 @ X61 ) @ X61 )
      | ~ ( v4_pre_topc @ X61 @ X62 )
      | ~ ( l1_pre_topc @ X62 ) ) ),
    inference(cnf,[status(esa)],[t69_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('69',plain,
    ( ( ( k2_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('71',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['22','36'])).

thf('73',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('75',plain,
    ( ( ( k4_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_tops_1 @ sk_A @ sk_B ) @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k4_xboole_0 @ X21 @ ( k4_xboole_0 @ X21 @ X22 ) )
      = ( k3_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k3_subset_1 @ X36 @ ( k3_subset_1 @ X36 @ X35 ) )
        = X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['78','83'])).

thf('85',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('87',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
      = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('91',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3','6'])).

thf('92',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k1_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('94',plain,
    ( ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
      = ( k2_tops_1 @ sk_A @ sk_B ) )
   <= ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['84','92','93'])).

thf('95',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
    | ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['95'])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t65_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_pre_topc @ A @ B )
            = ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) )).

thf('98',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( m1_subset_1 @ X59 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X60 ) ) )
      | ( ( k2_pre_topc @ X60 @ X59 )
        = ( k4_subset_1 @ ( u1_struct_0 @ X60 ) @ X59 @ ( k2_tops_1 @ X60 @ X59 ) ) )
      | ~ ( l1_pre_topc @ X60 ) ) ),
    inference(cnf,[status(esa)],[t65_tops_1])).

thf('99',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('103',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('104',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X30 @ X29 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('105',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k2_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['102','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('108',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X38 ) )
      | ( ( k4_subset_1 @ X38 @ X37 @ X39 )
        = ( k2_xboole_0 @ X37 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('112',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('113',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('115',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,
    ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_tops_1 @ sk_A @ sk_B ) )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['110','115'])).

thf('117',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['101','116'])).

thf('118',plain,(
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

thf('119',plain,(
    ! [X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X56 ) ) )
      | ~ ( v2_pre_topc @ X56 )
      | ( ( k2_pre_topc @ X56 @ X55 )
       != X55 )
      | ( v4_pre_topc @ X55 @ X56 )
      | ~ ( l1_pre_topc @ X56 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('120',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
     != sk_B ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( ( sk_B != sk_B )
      | ( v4_pre_topc @ sk_B @ sk_A ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['117','123'])).

thf('125',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,
    ( ~ ( v4_pre_topc @ sk_B @ sk_A )
   <= ~ ( v4_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['95'])).

thf('127',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v4_pre_topc @ sk_B @ sk_A )
    | ( ( k2_tops_1 @ sk_A @ sk_B )
      = ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['60'])).

thf('129',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['96','127','128'])).

thf('130',plain,
    ( ( k3_subset_1 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) )
    = ( k2_tops_1 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['94','129'])).

thf('131',plain,
    ( ( k2_tops_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','130'])).

thf('132',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(split,[status(esa)],['95'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('134',plain,
    ( ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) )
   <= ( ( k2_tops_1 @ sk_A @ sk_B )
     != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['96','127'])).

thf('136',plain,(
    ( k2_tops_1 @ sk_A @ sk_B )
 != ( k4_xboole_0 @ sk_B @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['131','136'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Z9Zpv0gGoa
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:45:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.42/1.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.42/1.67  % Solved by: fo/fo7.sh
% 1.42/1.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.42/1.67  % done 3753 iterations in 1.215s
% 1.42/1.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.42/1.67  % SZS output start Refutation
% 1.42/1.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.42/1.67  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 1.42/1.67  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.42/1.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.42/1.67  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.42/1.67  thf(k2_tops_1_type, type, k2_tops_1: $i > $i > $i).
% 1.42/1.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.42/1.67  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.42/1.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.42/1.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.42/1.67  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.42/1.67  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.42/1.67  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.42/1.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.42/1.67  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.42/1.67  thf(sk_B_type, type, sk_B: $i).
% 1.42/1.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.42/1.67  thf(sk_A_type, type, sk_A: $i).
% 1.42/1.67  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.42/1.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.42/1.67  thf(t77_tops_1, conjecture,
% 1.42/1.67    (![A:$i]:
% 1.42/1.67     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.42/1.67       ( ![B:$i]:
% 1.42/1.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.67           ( ( v4_pre_topc @ B @ A ) <=>
% 1.42/1.67             ( ( k2_tops_1 @ A @ B ) =
% 1.42/1.67               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ))).
% 1.42/1.67  thf(zf_stmt_0, negated_conjecture,
% 1.42/1.67    (~( ![A:$i]:
% 1.42/1.67        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.42/1.67          ( ![B:$i]:
% 1.42/1.67            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.67              ( ( v4_pre_topc @ B @ A ) <=>
% 1.42/1.67                ( ( k2_tops_1 @ A @ B ) =
% 1.42/1.67                  ( k7_subset_1 @
% 1.42/1.67                    ( u1_struct_0 @ A ) @ B @ ( k1_tops_1 @ A @ B ) ) ) ) ) ) ) )),
% 1.42/1.67    inference('cnf.neg', [status(esa)], [t77_tops_1])).
% 1.42/1.67  thf('0', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(t74_tops_1, axiom,
% 1.42/1.67    (![A:$i]:
% 1.42/1.67     ( ( l1_pre_topc @ A ) =>
% 1.42/1.67       ( ![B:$i]:
% 1.42/1.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.67           ( ( k1_tops_1 @ A @ B ) =
% 1.42/1.67             ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.42/1.67  thf('1', plain,
% 1.42/1.67      (![X63 : $i, X64 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X63 @ (k1_zfmisc_1 @ (u1_struct_0 @ X64)))
% 1.42/1.67          | ((k1_tops_1 @ X64 @ X63)
% 1.42/1.67              = (k7_subset_1 @ (u1_struct_0 @ X64) @ X63 @ 
% 1.42/1.67                 (k2_tops_1 @ X64 @ X63)))
% 1.42/1.67          | ~ (l1_pre_topc @ X64))),
% 1.42/1.67      inference('cnf', [status(esa)], [t74_tops_1])).
% 1.42/1.67  thf('2', plain,
% 1.42/1.67      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.67        | ((k1_tops_1 @ sk_A @ sk_B)
% 1.42/1.67            = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.67      inference('sup-', [status(thm)], ['0', '1'])).
% 1.42/1.67  thf('3', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('4', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(redefinition_k7_subset_1, axiom,
% 1.42/1.67    (![A:$i,B:$i,C:$i]:
% 1.42/1.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.67       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 1.42/1.67  thf('5', plain,
% 1.42/1.67      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41))
% 1.42/1.67          | ((k7_subset_1 @ X41 @ X40 @ X42) = (k4_xboole_0 @ X40 @ X42)))),
% 1.42/1.67      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 1.42/1.67  thf('6', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.67           = (k4_xboole_0 @ sk_B @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['4', '5'])).
% 1.42/1.67  thf('7', plain,
% 1.42/1.67      (((k1_tops_1 @ sk_A @ sk_B)
% 1.42/1.67         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.42/1.67  thf(t36_xboole_1, axiom,
% 1.42/1.67    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.42/1.67  thf('8', plain,
% 1.42/1.67      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.42/1.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.67  thf(t12_xboole_1, axiom,
% 1.42/1.67    (![A:$i,B:$i]:
% 1.42/1.67     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.42/1.67  thf('9', plain,
% 1.42/1.67      (![X6 : $i, X7 : $i]:
% 1.42/1.67         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.42/1.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.42/1.67  thf('10', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['8', '9'])).
% 1.42/1.67  thf(commutativity_k2_xboole_0, axiom,
% 1.42/1.67    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.42/1.67  thf('11', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.42/1.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.42/1.67  thf('12', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.42/1.67      inference('demod', [status(thm)], ['10', '11'])).
% 1.42/1.67  thf('13', plain,
% 1.42/1.67      (((k2_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)) = (sk_B))),
% 1.42/1.67      inference('sup+', [status(thm)], ['7', '12'])).
% 1.42/1.67  thf(dt_k2_subset_1, axiom,
% 1.42/1.67    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.42/1.67  thf('14', plain,
% 1.42/1.67      (![X26 : $i]: (m1_subset_1 @ (k2_subset_1 @ X26) @ (k1_zfmisc_1 @ X26))),
% 1.42/1.67      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.42/1.67  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.42/1.67  thf('15', plain, (![X23 : $i]: ((k2_subset_1 @ X23) = (X23))),
% 1.42/1.67      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.42/1.67  thf('16', plain, (![X26 : $i]: (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X26))),
% 1.42/1.67      inference('demod', [status(thm)], ['14', '15'])).
% 1.42/1.67  thf(d5_subset_1, axiom,
% 1.42/1.67    (![A:$i,B:$i]:
% 1.42/1.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.67       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.42/1.67  thf('17', plain,
% 1.42/1.67      (![X24 : $i, X25 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.42/1.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.42/1.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.67  thf('18', plain,
% 1.42/1.67      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['16', '17'])).
% 1.42/1.67  thf(t41_xboole_1, axiom,
% 1.42/1.67    (![A:$i,B:$i,C:$i]:
% 1.42/1.67     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 1.42/1.67       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 1.42/1.67  thf('19', plain,
% 1.42/1.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.42/1.67         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 1.42/1.67           = (k4_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 1.42/1.67      inference('cnf', [status(esa)], [t41_xboole_1])).
% 1.42/1.67  thf('20', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.42/1.67           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 1.42/1.67      inference('sup+', [status(thm)], ['18', '19'])).
% 1.42/1.67  thf(t39_xboole_1, axiom,
% 1.42/1.67    (![A:$i,B:$i]:
% 1.42/1.67     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.42/1.67  thf('21', plain,
% 1.42/1.67      (![X14 : $i, X15 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 1.42/1.67           = (k2_xboole_0 @ X14 @ X15))),
% 1.42/1.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.42/1.67  thf('22', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))
% 1.42/1.67           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.42/1.67      inference('demod', [status(thm)], ['20', '21'])).
% 1.42/1.67  thf(t4_subset_1, axiom,
% 1.42/1.67    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.42/1.67  thf('23', plain,
% 1.42/1.67      (![X46 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 1.42/1.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.42/1.67  thf(involutiveness_k3_subset_1, axiom,
% 1.42/1.67    (![A:$i,B:$i]:
% 1.42/1.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.67       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.42/1.67  thf('24', plain,
% 1.42/1.67      (![X35 : $i, X36 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 1.42/1.67          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 1.42/1.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.42/1.67  thf('25', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['23', '24'])).
% 1.42/1.67  thf('26', plain,
% 1.42/1.67      (![X46 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X46))),
% 1.42/1.67      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.42/1.67  thf('27', plain,
% 1.42/1.67      (![X24 : $i, X25 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.42/1.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.42/1.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.67  thf('28', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['26', '27'])).
% 1.42/1.67  thf('29', plain,
% 1.42/1.67      (![X14 : $i, X15 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 1.42/1.67           = (k2_xboole_0 @ X14 @ X15))),
% 1.42/1.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.42/1.67  thf('30', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ k1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 1.42/1.67           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['28', '29'])).
% 1.42/1.67  thf('31', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.42/1.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.42/1.67  thf(t1_boole, axiom,
% 1.42/1.67    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.42/1.67  thf('32', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 1.42/1.67      inference('cnf', [status(esa)], [t1_boole])).
% 1.42/1.67  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['31', '32'])).
% 1.42/1.67  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['31', '32'])).
% 1.42/1.67  thf('35', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 1.42/1.67      inference('demod', [status(thm)], ['30', '33', '34'])).
% 1.42/1.67  thf('36', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.42/1.67      inference('demod', [status(thm)], ['25', '35'])).
% 1.42/1.67  thf('37', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.42/1.67      inference('demod', [status(thm)], ['22', '36'])).
% 1.42/1.67  thf('38', plain,
% 1.42/1.67      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.42/1.67      inference('sup+', [status(thm)], ['13', '37'])).
% 1.42/1.67  thf(t48_xboole_1, axiom,
% 1.42/1.67    (![A:$i,B:$i]:
% 1.42/1.67     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.42/1.67  thf('39', plain,
% 1.42/1.67      (![X21 : $i, X22 : $i]:
% 1.42/1.67         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.42/1.67           = (k3_xboole_0 @ X21 @ X22))),
% 1.42/1.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.67  thf('40', plain,
% 1.42/1.67      (((k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.42/1.67         = (k3_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.42/1.67      inference('sup+', [status(thm)], ['38', '39'])).
% 1.42/1.67  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['31', '32'])).
% 1.42/1.67  thf('42', plain,
% 1.42/1.67      (![X14 : $i, X15 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 1.42/1.67           = (k2_xboole_0 @ X14 @ X15))),
% 1.42/1.67      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.42/1.67  thf('43', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['41', '42'])).
% 1.42/1.67  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['31', '32'])).
% 1.42/1.67  thf('45', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.42/1.67      inference('demod', [status(thm)], ['43', '44'])).
% 1.42/1.67  thf(commutativity_k3_xboole_0, axiom,
% 1.42/1.67    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.42/1.67  thf('46', plain,
% 1.42/1.67      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.42/1.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.42/1.67  thf('47', plain,
% 1.42/1.67      (((k1_tops_1 @ sk_A @ sk_B)
% 1.42/1.67         = (k3_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('demod', [status(thm)], ['40', '45', '46'])).
% 1.42/1.67  thf('48', plain,
% 1.42/1.67      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.42/1.67      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.42/1.67  thf(t3_subset, axiom,
% 1.42/1.67    (![A:$i,B:$i]:
% 1.42/1.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.42/1.67  thf('49', plain,
% 1.42/1.67      (![X49 : $i, X51 : $i]:
% 1.42/1.67         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 1.42/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.42/1.67  thf('50', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['48', '49'])).
% 1.42/1.67  thf('51', plain,
% 1.42/1.67      (![X35 : $i, X36 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 1.42/1.67          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 1.42/1.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.42/1.67  thf('52', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 1.42/1.67           = (k4_xboole_0 @ X0 @ X1))),
% 1.42/1.67      inference('sup-', [status(thm)], ['50', '51'])).
% 1.42/1.67  thf('53', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['48', '49'])).
% 1.42/1.67  thf('54', plain,
% 1.42/1.67      (![X24 : $i, X25 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.42/1.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.42/1.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.67  thf('55', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.42/1.67           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 1.42/1.67      inference('sup-', [status(thm)], ['53', '54'])).
% 1.42/1.67  thf('56', plain,
% 1.42/1.67      (![X21 : $i, X22 : $i]:
% 1.42/1.67         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.42/1.67           = (k3_xboole_0 @ X21 @ X22))),
% 1.42/1.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.67  thf('57', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 1.42/1.67           = (k3_xboole_0 @ X1 @ X0))),
% 1.42/1.67      inference('sup+', [status(thm)], ['55', '56'])).
% 1.42/1.67  thf('58', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.42/1.67           = (k4_xboole_0 @ X0 @ X1))),
% 1.42/1.67      inference('demod', [status(thm)], ['52', '57'])).
% 1.42/1.67  thf('59', plain,
% 1.42/1.67      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.42/1.67         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('sup+', [status(thm)], ['47', '58'])).
% 1.42/1.67  thf('60', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B)))
% 1.42/1.67        | (v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('61', plain,
% 1.42/1.67      (((v4_pre_topc @ sk_B @ sk_A)) <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('split', [status(esa)], ['60'])).
% 1.42/1.67  thf('62', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(t69_tops_1, axiom,
% 1.42/1.67    (![A:$i]:
% 1.42/1.67     ( ( l1_pre_topc @ A ) =>
% 1.42/1.67       ( ![B:$i]:
% 1.42/1.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.67           ( ( v4_pre_topc @ B @ A ) =>
% 1.42/1.67             ( r1_tarski @ ( k2_tops_1 @ A @ B ) @ B ) ) ) ) ))).
% 1.42/1.67  thf('63', plain,
% 1.42/1.67      (![X61 : $i, X62 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (u1_struct_0 @ X62)))
% 1.42/1.67          | (r1_tarski @ (k2_tops_1 @ X62 @ X61) @ X61)
% 1.42/1.67          | ~ (v4_pre_topc @ X61 @ X62)
% 1.42/1.67          | ~ (l1_pre_topc @ X62))),
% 1.42/1.67      inference('cnf', [status(esa)], [t69_tops_1])).
% 1.42/1.67  thf('64', plain,
% 1.42/1.67      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.67        | ~ (v4_pre_topc @ sk_B @ sk_A)
% 1.42/1.67        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.42/1.67      inference('sup-', [status(thm)], ['62', '63'])).
% 1.42/1.67  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('66', plain,
% 1.42/1.67      ((~ (v4_pre_topc @ sk_B @ sk_A)
% 1.42/1.67        | (r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))),
% 1.42/1.67      inference('demod', [status(thm)], ['64', '65'])).
% 1.42/1.67  thf('67', plain,
% 1.42/1.67      (((r1_tarski @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('sup-', [status(thm)], ['61', '66'])).
% 1.42/1.67  thf('68', plain,
% 1.42/1.67      (![X6 : $i, X7 : $i]:
% 1.42/1.67         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 1.42/1.67      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.42/1.67  thf('69', plain,
% 1.42/1.67      ((((k2_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B) = (sk_B)))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('sup-', [status(thm)], ['67', '68'])).
% 1.42/1.67  thf('70', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.42/1.67      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.42/1.67  thf('71', plain,
% 1.42/1.67      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['69', '70'])).
% 1.42/1.67  thf('72', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k1_xboole_0) = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.42/1.67      inference('demod', [status(thm)], ['22', '36'])).
% 1.42/1.67  thf('73', plain,
% 1.42/1.67      ((((k1_xboole_0) = (k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('sup+', [status(thm)], ['71', '72'])).
% 1.42/1.67  thf('74', plain,
% 1.42/1.67      (![X21 : $i, X22 : $i]:
% 1.42/1.67         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.42/1.67           = (k3_xboole_0 @ X21 @ X22))),
% 1.42/1.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.67  thf('75', plain,
% 1.42/1.67      ((((k4_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ k1_xboole_0)
% 1.42/1.67          = (k3_xboole_0 @ (k2_tops_1 @ sk_A @ sk_B) @ sk_B)))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('sup+', [status(thm)], ['73', '74'])).
% 1.42/1.67  thf('76', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.42/1.67      inference('demod', [status(thm)], ['43', '44'])).
% 1.42/1.67  thf('77', plain,
% 1.42/1.67      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.42/1.67      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.42/1.67  thf('78', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.42/1.67  thf('79', plain,
% 1.42/1.67      (![X21 : $i, X22 : $i]:
% 1.42/1.67         ((k4_xboole_0 @ X21 @ (k4_xboole_0 @ X21 @ X22))
% 1.42/1.67           = (k3_xboole_0 @ X21 @ X22))),
% 1.42/1.67      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.42/1.67  thf('80', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['48', '49'])).
% 1.42/1.67  thf('81', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.42/1.67      inference('sup+', [status(thm)], ['79', '80'])).
% 1.42/1.67  thf('82', plain,
% 1.42/1.67      (![X35 : $i, X36 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X36 @ (k3_subset_1 @ X36 @ X35)) = (X35))
% 1.42/1.67          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 1.42/1.67      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.42/1.67  thf('83', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1)))
% 1.42/1.67           = (k3_xboole_0 @ X0 @ X1))),
% 1.42/1.67      inference('sup-', [status(thm)], ['81', '82'])).
% 1.42/1.67  thf('84', plain,
% 1.42/1.67      ((((k3_subset_1 @ sk_B @ (k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.67          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('sup+', [status(thm)], ['78', '83'])).
% 1.42/1.67  thf('85', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.42/1.67  thf('86', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 1.42/1.67      inference('sup+', [status(thm)], ['79', '80'])).
% 1.42/1.67  thf('87', plain,
% 1.42/1.67      (![X24 : $i, X25 : $i]:
% 1.42/1.67         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 1.42/1.67          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 1.42/1.67      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.42/1.67  thf('88', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k3_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.42/1.67           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.42/1.67      inference('sup-', [status(thm)], ['86', '87'])).
% 1.42/1.67  thf('89', plain,
% 1.42/1.67      ((((k3_subset_1 @ sk_B @ (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.67          = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('sup+', [status(thm)], ['85', '88'])).
% 1.42/1.67  thf('90', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.42/1.67  thf('91', plain,
% 1.42/1.67      (((k1_tops_1 @ sk_A @ sk_B)
% 1.42/1.67         = (k4_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('demod', [status(thm)], ['2', '3', '6'])).
% 1.42/1.67  thf('92', plain,
% 1.42/1.67      ((((k3_subset_1 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.67          = (k1_tops_1 @ sk_A @ sk_B)))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.42/1.67  thf('93', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k3_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['75', '76', '77'])).
% 1.42/1.67  thf('94', plain,
% 1.42/1.67      ((((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.42/1.67          = (k2_tops_1 @ sk_A @ sk_B)))
% 1.42/1.67         <= (((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('demod', [status(thm)], ['84', '92', '93'])).
% 1.42/1.67  thf('95', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67              (k1_tops_1 @ sk_A @ sk_B)))
% 1.42/1.67        | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('96', plain,
% 1.42/1.67      (~
% 1.42/1.67       (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B)))) | 
% 1.42/1.67       ~ ((v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.67      inference('split', [status(esa)], ['95'])).
% 1.42/1.67  thf('97', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(t65_tops_1, axiom,
% 1.42/1.67    (![A:$i]:
% 1.42/1.67     ( ( l1_pre_topc @ A ) =>
% 1.42/1.67       ( ![B:$i]:
% 1.42/1.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.67           ( ( k2_pre_topc @ A @ B ) =
% 1.42/1.67             ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_tops_1 @ A @ B ) ) ) ) ) ))).
% 1.42/1.67  thf('98', plain,
% 1.42/1.67      (![X59 : $i, X60 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X59 @ (k1_zfmisc_1 @ (u1_struct_0 @ X60)))
% 1.42/1.67          | ((k2_pre_topc @ X60 @ X59)
% 1.42/1.67              = (k4_subset_1 @ (u1_struct_0 @ X60) @ X59 @ 
% 1.42/1.67                 (k2_tops_1 @ X60 @ X59)))
% 1.42/1.67          | ~ (l1_pre_topc @ X60))),
% 1.42/1.67      inference('cnf', [status(esa)], [t65_tops_1])).
% 1.42/1.67  thf('99', plain,
% 1.42/1.67      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.67        | ((k2_pre_topc @ sk_A @ sk_B)
% 1.42/1.67            = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67               (k2_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.67      inference('sup-', [status(thm)], ['97', '98'])).
% 1.42/1.67  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('101', plain,
% 1.42/1.67      (((k2_pre_topc @ sk_A @ sk_B)
% 1.42/1.67         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67            (k2_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('demod', [status(thm)], ['99', '100'])).
% 1.42/1.67  thf('102', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('split', [status(esa)], ['60'])).
% 1.42/1.67  thf('103', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(dt_k7_subset_1, axiom,
% 1.42/1.67    (![A:$i,B:$i,C:$i]:
% 1.42/1.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.42/1.67       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.42/1.67  thf('104', plain,
% 1.42/1.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 1.42/1.67          | (m1_subset_1 @ (k7_subset_1 @ X30 @ X29 @ X31) @ 
% 1.42/1.67             (k1_zfmisc_1 @ X30)))),
% 1.42/1.67      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 1.42/1.67  thf('105', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 1.42/1.67          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('sup-', [status(thm)], ['103', '104'])).
% 1.42/1.67  thf('106', plain,
% 1.42/1.67      (((m1_subset_1 @ (k2_tops_1 @ sk_A @ sk_B) @ 
% 1.42/1.67         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('sup+', [status(thm)], ['102', '105'])).
% 1.42/1.67  thf('107', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(redefinition_k4_subset_1, axiom,
% 1.42/1.67    (![A:$i,B:$i,C:$i]:
% 1.42/1.67     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.42/1.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.42/1.67       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.42/1.67  thf('108', plain,
% 1.42/1.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X38))
% 1.42/1.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X38))
% 1.42/1.67          | ((k4_subset_1 @ X38 @ X37 @ X39) = (k2_xboole_0 @ X37 @ X39)))),
% 1.42/1.67      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.42/1.67  thf('109', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.67            = (k2_xboole_0 @ sk_B @ X0))
% 1.42/1.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.42/1.67      inference('sup-', [status(thm)], ['107', '108'])).
% 1.42/1.67  thf('110', plain,
% 1.42/1.67      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.67          = (k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('sup-', [status(thm)], ['106', '109'])).
% 1.42/1.67  thf('111', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.67           = (k4_xboole_0 @ sk_B @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['4', '5'])).
% 1.42/1.67  thf('112', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('split', [status(esa)], ['60'])).
% 1.42/1.67  thf('113', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('sup+', [status(thm)], ['111', '112'])).
% 1.42/1.67  thf('114', plain,
% 1.42/1.67      (![X0 : $i, X1 : $i]:
% 1.42/1.67         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 1.42/1.67      inference('demod', [status(thm)], ['10', '11'])).
% 1.42/1.67  thf('115', plain,
% 1.42/1.67      ((((k2_xboole_0 @ sk_B @ (k2_tops_1 @ sk_A @ sk_B)) = (sk_B)))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('sup+', [status(thm)], ['113', '114'])).
% 1.42/1.67  thf('116', plain,
% 1.42/1.67      ((((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ (k2_tops_1 @ sk_A @ sk_B))
% 1.42/1.67          = (sk_B)))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('demod', [status(thm)], ['110', '115'])).
% 1.42/1.67  thf('117', plain,
% 1.42/1.67      ((((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('sup+', [status(thm)], ['101', '116'])).
% 1.42/1.67  thf('118', plain,
% 1.42/1.67      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf(t52_pre_topc, axiom,
% 1.42/1.67    (![A:$i]:
% 1.42/1.67     ( ( l1_pre_topc @ A ) =>
% 1.42/1.67       ( ![B:$i]:
% 1.42/1.67         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.42/1.67           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.42/1.67             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.42/1.67               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.42/1.67  thf('119', plain,
% 1.42/1.67      (![X55 : $i, X56 : $i]:
% 1.42/1.67         (~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (u1_struct_0 @ X56)))
% 1.42/1.67          | ~ (v2_pre_topc @ X56)
% 1.42/1.67          | ((k2_pre_topc @ X56 @ X55) != (X55))
% 1.42/1.67          | (v4_pre_topc @ X55 @ X56)
% 1.42/1.67          | ~ (l1_pre_topc @ X56))),
% 1.42/1.67      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.42/1.67  thf('120', plain,
% 1.42/1.67      ((~ (l1_pre_topc @ sk_A)
% 1.42/1.67        | (v4_pre_topc @ sk_B @ sk_A)
% 1.42/1.67        | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B))
% 1.42/1.67        | ~ (v2_pre_topc @ sk_A))),
% 1.42/1.67      inference('sup-', [status(thm)], ['118', '119'])).
% 1.42/1.67  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('122', plain, ((v2_pre_topc @ sk_A)),
% 1.42/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.42/1.67  thf('123', plain,
% 1.42/1.67      (((v4_pre_topc @ sk_B @ sk_A) | ((k2_pre_topc @ sk_A @ sk_B) != (sk_B)))),
% 1.42/1.67      inference('demod', [status(thm)], ['120', '121', '122'])).
% 1.42/1.67  thf('124', plain,
% 1.42/1.67      (((((sk_B) != (sk_B)) | (v4_pre_topc @ sk_B @ sk_A)))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('sup-', [status(thm)], ['117', '123'])).
% 1.42/1.67  thf('125', plain,
% 1.42/1.67      (((v4_pre_topc @ sk_B @ sk_A))
% 1.42/1.67         <= ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('simplify', [status(thm)], ['124'])).
% 1.42/1.67  thf('126', plain,
% 1.42/1.67      ((~ (v4_pre_topc @ sk_B @ sk_A)) <= (~ ((v4_pre_topc @ sk_B @ sk_A)))),
% 1.42/1.67      inference('split', [status(esa)], ['95'])).
% 1.42/1.67  thf('127', plain,
% 1.42/1.67      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.42/1.67       ~
% 1.42/1.67       (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.67      inference('sup-', [status(thm)], ['125', '126'])).
% 1.42/1.67  thf('128', plain,
% 1.42/1.67      (((v4_pre_topc @ sk_B @ sk_A)) | 
% 1.42/1.67       (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.67      inference('split', [status(esa)], ['60'])).
% 1.42/1.67  thf('129', plain, (((v4_pre_topc @ sk_B @ sk_A))),
% 1.42/1.67      inference('sat_resolution*', [status(thm)], ['96', '127', '128'])).
% 1.42/1.67  thf('130', plain,
% 1.42/1.67      (((k3_subset_1 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))
% 1.42/1.67         = (k2_tops_1 @ sk_A @ sk_B))),
% 1.42/1.67      inference('simpl_trail', [status(thm)], ['94', '129'])).
% 1.42/1.67  thf('131', plain,
% 1.42/1.67      (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67         = (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('demod', [status(thm)], ['59', '130'])).
% 1.42/1.67  thf('132', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          != (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67              (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (~
% 1.42/1.67             (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('split', [status(esa)], ['95'])).
% 1.42/1.67  thf('133', plain,
% 1.42/1.67      (![X0 : $i]:
% 1.42/1.67         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 1.42/1.67           = (k4_xboole_0 @ sk_B @ X0))),
% 1.42/1.67      inference('sup-', [status(thm)], ['4', '5'])).
% 1.42/1.67  thf('134', plain,
% 1.42/1.67      ((((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B))))
% 1.42/1.67         <= (~
% 1.42/1.67             (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67                = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67                   (k1_tops_1 @ sk_A @ sk_B)))))),
% 1.42/1.67      inference('demod', [status(thm)], ['132', '133'])).
% 1.42/1.67  thf('135', plain,
% 1.42/1.67      (~
% 1.42/1.67       (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67          = (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.42/1.67             (k1_tops_1 @ sk_A @ sk_B))))),
% 1.42/1.67      inference('sat_resolution*', [status(thm)], ['96', '127'])).
% 1.42/1.67  thf('136', plain,
% 1.42/1.67      (((k2_tops_1 @ sk_A @ sk_B)
% 1.42/1.67         != (k4_xboole_0 @ sk_B @ (k1_tops_1 @ sk_A @ sk_B)))),
% 1.42/1.67      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 1.42/1.67  thf('137', plain, ($false),
% 1.42/1.67      inference('simplify_reflect-', [status(thm)], ['131', '136'])).
% 1.42/1.67  
% 1.42/1.67  % SZS output end Refutation
% 1.42/1.67  
% 1.42/1.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
