%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dAf8Ub8zNx

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:52 EST 2020

% Result     : Theorem 10.04s
% Output     : Refutation 10.04s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 231 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :   20
%              Number of atoms          :  908 (1736 expanded)
%              Number of equality atoms :   66 ( 104 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) )
      | ( ( k4_subset_1 @ X30 @ X29 @ X31 )
        = ( k2_xboole_0 @ X29 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ ( k2_xboole_0 @ X12 @ X13 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r2_hidden @ X14 @ X16 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('31',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X28 @ ( k3_subset_1 @ X28 @ X27 ) )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( r1_tarski @ X17 @ X15 )
      | ( X16
       != ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('41',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','44'])).

thf('46',plain,(
    ! [X32: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('58',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('60',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('62',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('72',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('74',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X15: $i,X17: $i] :
      ( ( r1_tarski @ X17 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('76',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('78',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['69','80'])).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_xboole_0 @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) )
      = ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('83',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('89',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ( m1_subset_1 @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X26: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('97',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('99',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k4_xboole_0 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_subset_1 @ X22 @ X23 )
        = ( k4_xboole_0 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('103',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['97','100','103'])).

thf('105',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['8','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dAf8Ub8zNx
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 09:37:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 10.04/10.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.04/10.22  % Solved by: fo/fo7.sh
% 10.04/10.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.04/10.22  % done 9890 iterations in 9.776s
% 10.04/10.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.04/10.22  % SZS output start Refutation
% 10.04/10.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.04/10.22  thf(sk_C_1_type, type, sk_C_1: $i).
% 10.04/10.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.04/10.22  thf(sk_B_type, type, sk_B: $i).
% 10.04/10.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.04/10.22  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.04/10.22  thf(sk_A_type, type, sk_A: $i).
% 10.04/10.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.04/10.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.04/10.22  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.04/10.22  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 10.04/10.22  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 10.04/10.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.04/10.22  thf(t41_subset_1, conjecture,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.04/10.22       ( ![C:$i]:
% 10.04/10.22         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.04/10.22           ( r1_tarski @
% 10.04/10.22             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 10.04/10.22             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 10.04/10.22  thf(zf_stmt_0, negated_conjecture,
% 10.04/10.22    (~( ![A:$i,B:$i]:
% 10.04/10.22        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.04/10.22          ( ![C:$i]:
% 10.04/10.22            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.04/10.22              ( r1_tarski @
% 10.04/10.22                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 10.04/10.22                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 10.04/10.22    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 10.04/10.22  thf('0', plain,
% 10.04/10.22      (~ (r1_tarski @ 
% 10.04/10.22          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 10.04/10.22          (k3_subset_1 @ sk_A @ sk_B))),
% 10.04/10.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.04/10.22  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.04/10.22  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.04/10.22  thf(redefinition_k4_subset_1, axiom,
% 10.04/10.22    (![A:$i,B:$i,C:$i]:
% 10.04/10.22     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 10.04/10.22         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 10.04/10.22       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 10.04/10.22  thf('3', plain,
% 10.04/10.22      (![X29 : $i, X30 : $i, X31 : $i]:
% 10.04/10.22         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 10.04/10.22          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30))
% 10.04/10.22          | ((k4_subset_1 @ X30 @ X29 @ X31) = (k2_xboole_0 @ X29 @ X31)))),
% 10.04/10.22      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 10.04/10.22  thf('4', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 10.04/10.22          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['2', '3'])).
% 10.04/10.22  thf('5', plain,
% 10.04/10.22      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 10.04/10.22      inference('sup-', [status(thm)], ['1', '4'])).
% 10.04/10.22  thf(commutativity_k2_xboole_0, axiom,
% 10.04/10.22    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 10.04/10.22  thf('6', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.04/10.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.04/10.22  thf('7', plain,
% 10.04/10.22      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 10.04/10.22      inference('demod', [status(thm)], ['5', '6'])).
% 10.04/10.22  thf('8', plain,
% 10.04/10.22      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 10.04/10.22          (k3_subset_1 @ sk_A @ sk_B))),
% 10.04/10.22      inference('demod', [status(thm)], ['0', '7'])).
% 10.04/10.22  thf(t36_xboole_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 10.04/10.22  thf('9', plain,
% 10.04/10.22      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 10.04/10.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.04/10.22  thf(t12_xboole_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 10.04/10.22  thf('10', plain,
% 10.04/10.22      (![X2 : $i, X3 : $i]:
% 10.04/10.22         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.04/10.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.04/10.22  thf('11', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['9', '10'])).
% 10.04/10.22  thf('12', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.04/10.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.04/10.22  thf('13', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 10.04/10.22      inference('demod', [status(thm)], ['11', '12'])).
% 10.04/10.22  thf(t39_xboole_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 10.04/10.22  thf('14', plain,
% 10.04/10.22      (![X6 : $i, X7 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 10.04/10.22           = (k2_xboole_0 @ X6 @ X7))),
% 10.04/10.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.04/10.22  thf('15', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 10.04/10.22      inference('sup+', [status(thm)], ['13', '14'])).
% 10.04/10.22  thf('16', plain,
% 10.04/10.22      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 10.04/10.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.04/10.22  thf(t44_xboole_1, axiom,
% 10.04/10.22    (![A:$i,B:$i,C:$i]:
% 10.04/10.22     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 10.04/10.22       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 10.04/10.22  thf('17', plain,
% 10.04/10.22      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.04/10.22         ((r1_tarski @ X11 @ (k2_xboole_0 @ X12 @ X13))
% 10.04/10.22          | ~ (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X13))),
% 10.04/10.22      inference('cnf', [status(esa)], [t44_xboole_1])).
% 10.04/10.22  thf('18', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['16', '17'])).
% 10.04/10.22  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 10.04/10.22      inference('sup+', [status(thm)], ['15', '18'])).
% 10.04/10.22  thf(d1_zfmisc_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 10.04/10.22       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 10.04/10.22  thf('20', plain,
% 10.04/10.22      (![X14 : $i, X15 : $i, X16 : $i]:
% 10.04/10.22         (~ (r1_tarski @ X14 @ X15)
% 10.04/10.22          | (r2_hidden @ X14 @ X16)
% 10.04/10.22          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 10.04/10.22      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.04/10.22  thf('21', plain,
% 10.04/10.22      (![X14 : $i, X15 : $i]:
% 10.04/10.22         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 10.04/10.22      inference('simplify', [status(thm)], ['20'])).
% 10.04/10.22  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['19', '21'])).
% 10.04/10.22  thf(d2_subset_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( ( v1_xboole_0 @ A ) =>
% 10.04/10.22         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 10.04/10.22       ( ( ~( v1_xboole_0 @ A ) ) =>
% 10.04/10.22         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 10.04/10.22  thf('23', plain,
% 10.04/10.22      (![X19 : $i, X20 : $i]:
% 10.04/10.22         (~ (r2_hidden @ X19 @ X20)
% 10.04/10.22          | (m1_subset_1 @ X19 @ X20)
% 10.04/10.22          | (v1_xboole_0 @ X20))),
% 10.04/10.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.04/10.22  thf('24', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 10.04/10.22          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['22', '23'])).
% 10.04/10.22  thf(fc1_subset_1, axiom,
% 10.04/10.22    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 10.04/10.22  thf('25', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 10.04/10.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.04/10.22  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.04/10.22      inference('clc', [status(thm)], ['24', '25'])).
% 10.04/10.22  thf(d5_subset_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.04/10.22       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 10.04/10.22  thf('27', plain,
% 10.04/10.22      (![X22 : $i, X23 : $i]:
% 10.04/10.22         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 10.04/10.22          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 10.04/10.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.04/10.22  thf('28', plain,
% 10.04/10.22      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['26', '27'])).
% 10.04/10.22  thf(t41_xboole_1, axiom,
% 10.04/10.22    (![A:$i,B:$i,C:$i]:
% 10.04/10.22     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 10.04/10.22       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 10.04/10.22  thf('29', plain,
% 10.04/10.22      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 10.04/10.22           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 10.04/10.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.04/10.22  thf('30', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 10.04/10.22           = (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 10.04/10.22      inference('sup+', [status(thm)], ['28', '29'])).
% 10.04/10.22  thf(t4_subset_1, axiom,
% 10.04/10.22    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 10.04/10.22  thf('31', plain,
% 10.04/10.22      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 10.04/10.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.04/10.22  thf(involutiveness_k3_subset_1, axiom,
% 10.04/10.22    (![A:$i,B:$i]:
% 10.04/10.22     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.04/10.22       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 10.04/10.22  thf('32', plain,
% 10.04/10.22      (![X27 : $i, X28 : $i]:
% 10.04/10.22         (((k3_subset_1 @ X28 @ (k3_subset_1 @ X28 @ X27)) = (X27))
% 10.04/10.22          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 10.04/10.22      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 10.04/10.22  thf('33', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['31', '32'])).
% 10.04/10.22  thf('34', plain,
% 10.04/10.22      (![X6 : $i, X7 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 10.04/10.22           = (k2_xboole_0 @ X6 @ X7))),
% 10.04/10.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.04/10.22  thf('35', plain,
% 10.04/10.22      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 10.04/10.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.04/10.22  thf('36', plain,
% 10.04/10.22      (![X19 : $i, X20 : $i]:
% 10.04/10.22         (~ (m1_subset_1 @ X19 @ X20)
% 10.04/10.22          | (r2_hidden @ X19 @ X20)
% 10.04/10.22          | (v1_xboole_0 @ X20))),
% 10.04/10.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.04/10.22  thf('37', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 10.04/10.22          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['35', '36'])).
% 10.04/10.22  thf('38', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 10.04/10.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.04/10.22  thf('39', plain,
% 10.04/10.22      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.04/10.22      inference('clc', [status(thm)], ['37', '38'])).
% 10.04/10.22  thf('40', plain,
% 10.04/10.22      (![X15 : $i, X16 : $i, X17 : $i]:
% 10.04/10.22         (~ (r2_hidden @ X17 @ X16)
% 10.04/10.22          | (r1_tarski @ X17 @ X15)
% 10.04/10.22          | ((X16) != (k1_zfmisc_1 @ X15)))),
% 10.04/10.22      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.04/10.22  thf('41', plain,
% 10.04/10.22      (![X15 : $i, X17 : $i]:
% 10.04/10.22         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 10.04/10.22      inference('simplify', [status(thm)], ['40'])).
% 10.04/10.22  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.04/10.22      inference('sup-', [status(thm)], ['39', '41'])).
% 10.04/10.22  thf('43', plain,
% 10.04/10.22      (![X2 : $i, X3 : $i]:
% 10.04/10.22         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.04/10.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.04/10.22  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['42', '43'])).
% 10.04/10.22  thf('45', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 10.04/10.22      inference('sup+', [status(thm)], ['34', '44'])).
% 10.04/10.22  thf('46', plain,
% 10.04/10.22      (![X32 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 10.04/10.22      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.04/10.22  thf('47', plain,
% 10.04/10.22      (![X22 : $i, X23 : $i]:
% 10.04/10.22         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 10.04/10.22          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 10.04/10.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.04/10.22  thf('48', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['46', '47'])).
% 10.04/10.22  thf('49', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 10.04/10.22      inference('demod', [status(thm)], ['45', '48'])).
% 10.04/10.22  thf('50', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['42', '43'])).
% 10.04/10.22  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 10.04/10.22      inference('sup+', [status(thm)], ['49', '50'])).
% 10.04/10.22  thf('52', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 10.04/10.22      inference('demod', [status(thm)], ['33', '51'])).
% 10.04/10.22  thf('53', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 10.04/10.22           = (k1_xboole_0))),
% 10.04/10.22      inference('demod', [status(thm)], ['30', '52'])).
% 10.04/10.22  thf('54', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.04/10.22  thf('55', plain,
% 10.04/10.22      (![X19 : $i, X20 : $i]:
% 10.04/10.22         (~ (m1_subset_1 @ X19 @ X20)
% 10.04/10.22          | (r2_hidden @ X19 @ X20)
% 10.04/10.22          | (v1_xboole_0 @ X20))),
% 10.04/10.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.04/10.22  thf('56', plain,
% 10.04/10.22      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 10.04/10.22        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['54', '55'])).
% 10.04/10.22  thf('57', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 10.04/10.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.04/10.22  thf('58', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('clc', [status(thm)], ['56', '57'])).
% 10.04/10.22  thf('59', plain,
% 10.04/10.22      (![X15 : $i, X17 : $i]:
% 10.04/10.22         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 10.04/10.22      inference('simplify', [status(thm)], ['40'])).
% 10.04/10.22  thf('60', plain, ((r1_tarski @ sk_B @ sk_A)),
% 10.04/10.22      inference('sup-', [status(thm)], ['58', '59'])).
% 10.04/10.22  thf('61', plain,
% 10.04/10.22      (![X2 : $i, X3 : $i]:
% 10.04/10.22         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.04/10.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.04/10.22  thf('62', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 10.04/10.22      inference('sup-', [status(thm)], ['60', '61'])).
% 10.04/10.22  thf('63', plain,
% 10.04/10.22      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 10.04/10.22           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 10.04/10.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.04/10.22  thf('64', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 10.04/10.22           = (k4_xboole_0 @ X0 @ sk_A))),
% 10.04/10.22      inference('sup+', [status(thm)], ['62', '63'])).
% 10.04/10.22  thf('65', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ k1_xboole_0 @ sk_A)
% 10.04/10.22           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 10.04/10.22              sk_A))),
% 10.04/10.22      inference('sup+', [status(thm)], ['53', '64'])).
% 10.04/10.22  thf('66', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['42', '43'])).
% 10.04/10.22  thf('67', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 10.04/10.22      inference('demod', [status(thm)], ['11', '12'])).
% 10.04/10.22  thf('68', plain,
% 10.04/10.22      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 10.04/10.22      inference('sup+', [status(thm)], ['66', '67'])).
% 10.04/10.22  thf('69', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k1_xboole_0)
% 10.04/10.22           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 10.04/10.22              sk_A))),
% 10.04/10.22      inference('demod', [status(thm)], ['65', '68'])).
% 10.04/10.22  thf('70', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.04/10.22  thf('71', plain,
% 10.04/10.22      (![X19 : $i, X20 : $i]:
% 10.04/10.22         (~ (m1_subset_1 @ X19 @ X20)
% 10.04/10.22          | (r2_hidden @ X19 @ X20)
% 10.04/10.22          | (v1_xboole_0 @ X20))),
% 10.04/10.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.04/10.22  thf('72', plain,
% 10.04/10.22      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 10.04/10.22        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['70', '71'])).
% 10.04/10.22  thf('73', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 10.04/10.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.04/10.22  thf('74', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('clc', [status(thm)], ['72', '73'])).
% 10.04/10.22  thf('75', plain,
% 10.04/10.22      (![X15 : $i, X17 : $i]:
% 10.04/10.22         ((r1_tarski @ X17 @ X15) | ~ (r2_hidden @ X17 @ (k1_zfmisc_1 @ X15)))),
% 10.04/10.22      inference('simplify', [status(thm)], ['40'])).
% 10.04/10.22  thf('76', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 10.04/10.22      inference('sup-', [status(thm)], ['74', '75'])).
% 10.04/10.22  thf('77', plain,
% 10.04/10.22      (![X2 : $i, X3 : $i]:
% 10.04/10.22         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.04/10.22      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.04/10.22  thf('78', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 10.04/10.22      inference('sup-', [status(thm)], ['76', '77'])).
% 10.04/10.22  thf('79', plain,
% 10.04/10.22      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 10.04/10.22           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 10.04/10.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.04/10.22  thf('80', plain,
% 10.04/10.22      (![X0 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_A)
% 10.04/10.22           = (k4_xboole_0 @ X0 @ sk_A))),
% 10.04/10.22      inference('sup+', [status(thm)], ['78', '79'])).
% 10.04/10.22  thf('81', plain,
% 10.04/10.22      (((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A))),
% 10.04/10.22      inference('sup+', [status(thm)], ['69', '80'])).
% 10.04/10.22  thf('82', plain,
% 10.04/10.22      (![X6 : $i, X7 : $i]:
% 10.04/10.22         ((k2_xboole_0 @ X6 @ (k4_xboole_0 @ X7 @ X6))
% 10.04/10.22           = (k2_xboole_0 @ X6 @ X7))),
% 10.04/10.22      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.04/10.22  thf('83', plain,
% 10.04/10.22      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 10.04/10.22         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 10.04/10.22      inference('sup+', [status(thm)], ['81', '82'])).
% 10.04/10.22  thf('84', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['42', '43'])).
% 10.04/10.22  thf('85', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.04/10.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.04/10.22  thf('86', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.04/10.22      inference('sup+', [status(thm)], ['84', '85'])).
% 10.04/10.22  thf('87', plain,
% 10.04/10.22      (((sk_A) = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 10.04/10.22      inference('demod', [status(thm)], ['83', '86'])).
% 10.04/10.22  thf('88', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 10.04/10.22      inference('sup-', [status(thm)], ['16', '17'])).
% 10.04/10.22  thf('89', plain,
% 10.04/10.22      (![X14 : $i, X15 : $i]:
% 10.04/10.22         ((r2_hidden @ X14 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X14 @ X15))),
% 10.04/10.22      inference('simplify', [status(thm)], ['20'])).
% 10.04/10.22  thf('90', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['88', '89'])).
% 10.04/10.22  thf('91', plain,
% 10.04/10.22      (![X19 : $i, X20 : $i]:
% 10.04/10.22         (~ (r2_hidden @ X19 @ X20)
% 10.04/10.22          | (m1_subset_1 @ X19 @ X20)
% 10.04/10.22          | (v1_xboole_0 @ X20))),
% 10.04/10.22      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.04/10.22  thf('92', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 10.04/10.22          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 10.04/10.22      inference('sup-', [status(thm)], ['90', '91'])).
% 10.04/10.22  thf('93', plain, (![X26 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X26))),
% 10.04/10.22      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.04/10.22  thf('94', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]:
% 10.04/10.22         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.04/10.22      inference('clc', [status(thm)], ['92', '93'])).
% 10.04/10.22  thf('95', plain,
% 10.04/10.22      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('sup+', [status(thm)], ['87', '94'])).
% 10.04/10.22  thf('96', plain,
% 10.04/10.22      (![X22 : $i, X23 : $i]:
% 10.04/10.22         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 10.04/10.22          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 10.04/10.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.04/10.22  thf('97', plain,
% 10.04/10.22      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 10.04/10.22         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 10.04/10.22      inference('sup-', [status(thm)], ['95', '96'])).
% 10.04/10.22  thf('98', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.04/10.22      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.04/10.22  thf('99', plain,
% 10.04/10.22      (![X8 : $i, X9 : $i, X10 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X10)
% 10.04/10.22           = (k4_xboole_0 @ X8 @ (k2_xboole_0 @ X9 @ X10)))),
% 10.04/10.22      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.04/10.22  thf('100', plain,
% 10.04/10.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.04/10.22         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 10.04/10.22           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.04/10.22      inference('sup+', [status(thm)], ['98', '99'])).
% 10.04/10.22  thf('101', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.04/10.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.04/10.22  thf('102', plain,
% 10.04/10.22      (![X22 : $i, X23 : $i]:
% 10.04/10.22         (((k3_subset_1 @ X22 @ X23) = (k4_xboole_0 @ X22 @ X23))
% 10.04/10.22          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X22)))),
% 10.04/10.22      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.04/10.22  thf('103', plain,
% 10.04/10.22      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.04/10.22      inference('sup-', [status(thm)], ['101', '102'])).
% 10.04/10.22  thf('104', plain,
% 10.04/10.22      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 10.04/10.22         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 10.04/10.22      inference('demod', [status(thm)], ['97', '100', '103'])).
% 10.04/10.22  thf('105', plain,
% 10.04/10.22      (![X4 : $i, X5 : $i]: (r1_tarski @ (k4_xboole_0 @ X4 @ X5) @ X4)),
% 10.04/10.22      inference('cnf', [status(esa)], [t36_xboole_1])).
% 10.04/10.22  thf('106', plain, ($false),
% 10.04/10.22      inference('demod', [status(thm)], ['8', '104', '105'])).
% 10.04/10.22  
% 10.04/10.22  % SZS output end Refutation
% 10.04/10.22  
% 10.04/10.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
