%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TdIptL78is

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:52 EST 2020

% Result     : Theorem 10.54s
% Output     : Refutation 10.61s
% Verified   : 
% Statistics : Number of formulae       :  203 ( 986 expanded)
%              Number of leaves         :   28 ( 328 expanded)
%              Depth                    :   24
%              Number of atoms          : 1511 (7259 expanded)
%              Number of equality atoms :  111 ( 468 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) )
      | ( ( k4_subset_1 @ X33 @ X32 @ X34 )
        = ( k2_xboole_0 @ X32 @ X34 ) ) ) ),
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

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X27 @ X28 ) @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('20',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('23',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 )
      = ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('37',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X31 @ ( k3_subset_1 @ X31 @ X30 ) )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','26','27'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('46',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('48',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('50',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('57',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('59',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X5 ) @ ( k4_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_A ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','82'])).

thf('84',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['41','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('86',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('88',plain,
    ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('95',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('98',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['93','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','26','27'])).

thf('106',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('108',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('109',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X5 ) @ ( k4_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('110',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k4_xboole_0 @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['103','106'])).

thf('115',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('121',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['102','121'])).

thf('123',plain,(
    ! [X0: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X0 ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('124',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r2_hidden @ X17 @ X19 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('125',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','125'])).

thf('127',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['122','132'])).

thf('134',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) )
      = ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('139',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r2_hidden @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( m1_subset_1 @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','144'])).

thf('146',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['92','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['16','26','27'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('150',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('152',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('154',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['150','151','154'])).

thf('156',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('158',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('160',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['74','81'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup+',[status(thm)],['158','161'])).

thf('163',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(demod,[status(thm)],['155','162'])).

thf('164',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('165',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('167',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X5 ) @ ( k4_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k4_xboole_0 @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169'])).

thf('171',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['165','170'])).

thf('172',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['164','171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['8','163','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TdIptL78is
% 0.11/0.35  % Computer   : n012.cluster.edu
% 0.11/0.35  % Model      : x86_64 x86_64
% 0.11/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.35  % Memory     : 8042.1875MB
% 0.11/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.35  % CPULimit   : 60
% 0.11/0.35  % DateTime   : Tue Dec  1 12:01:22 EST 2020
% 0.11/0.35  % CPUTime    : 
% 0.11/0.35  % Running portfolio for 600 s
% 0.11/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.35  % Number of cores: 8
% 0.11/0.35  % Python version: Python 3.6.8
% 0.11/0.35  % Running in FO mode
% 10.54/10.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.54/10.78  % Solved by: fo/fo7.sh
% 10.54/10.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.54/10.78  % done 11351 iterations in 10.316s
% 10.54/10.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.54/10.78  % SZS output start Refutation
% 10.54/10.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.54/10.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 10.54/10.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.54/10.78  thf(sk_A_type, type, sk_A: $i).
% 10.54/10.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.54/10.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 10.54/10.78  thf(sk_B_type, type, sk_B: $i).
% 10.54/10.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.54/10.78  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 10.54/10.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 10.54/10.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.54/10.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.54/10.78  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 10.54/10.78  thf(t41_subset_1, conjecture,
% 10.54/10.78    (![A:$i,B:$i]:
% 10.54/10.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.54/10.78       ( ![C:$i]:
% 10.54/10.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.54/10.78           ( r1_tarski @
% 10.54/10.78             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 10.54/10.78             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 10.54/10.78  thf(zf_stmt_0, negated_conjecture,
% 10.54/10.78    (~( ![A:$i,B:$i]:
% 10.54/10.78        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.54/10.78          ( ![C:$i]:
% 10.54/10.78            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 10.54/10.78              ( r1_tarski @
% 10.54/10.78                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 10.54/10.78                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 10.54/10.78    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 10.54/10.78  thf('0', plain,
% 10.54/10.78      (~ (r1_tarski @ 
% 10.54/10.78          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 10.54/10.78          (k3_subset_1 @ sk_A @ sk_B))),
% 10.54/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.78  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.54/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.78  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.54/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.54/10.78  thf(redefinition_k4_subset_1, axiom,
% 10.54/10.78    (![A:$i,B:$i,C:$i]:
% 10.54/10.78     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 10.54/10.78         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 10.54/10.78       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 10.54/10.78  thf('3', plain,
% 10.54/10.78      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.54/10.78         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 10.54/10.78          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33))
% 10.54/10.78          | ((k4_subset_1 @ X33 @ X32 @ X34) = (k2_xboole_0 @ X32 @ X34)))),
% 10.54/10.78      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 10.54/10.78  thf('4', plain,
% 10.54/10.78      (![X0 : $i]:
% 10.54/10.78         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 10.54/10.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 10.54/10.78      inference('sup-', [status(thm)], ['2', '3'])).
% 10.54/10.78  thf('5', plain,
% 10.54/10.78      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 10.54/10.78      inference('sup-', [status(thm)], ['1', '4'])).
% 10.54/10.78  thf(commutativity_k2_xboole_0, axiom,
% 10.54/10.78    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 10.54/10.78  thf('6', plain,
% 10.54/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.54/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.54/10.78  thf('7', plain,
% 10.54/10.78      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 10.54/10.78      inference('demod', [status(thm)], ['5', '6'])).
% 10.54/10.78  thf('8', plain,
% 10.54/10.78      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 10.54/10.78          (k3_subset_1 @ sk_A @ sk_B))),
% 10.54/10.78      inference('demod', [status(thm)], ['0', '7'])).
% 10.54/10.78  thf(t4_subset_1, axiom,
% 10.54/10.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 10.54/10.78  thf('9', plain,
% 10.54/10.78      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 10.54/10.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.54/10.78  thf(dt_k3_subset_1, axiom,
% 10.54/10.78    (![A:$i,B:$i]:
% 10.54/10.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.54/10.78       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 10.54/10.78  thf('10', plain,
% 10.54/10.78      (![X27 : $i, X28 : $i]:
% 10.54/10.78         ((m1_subset_1 @ (k3_subset_1 @ X27 @ X28) @ (k1_zfmisc_1 @ X27))
% 10.54/10.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 10.61/10.78      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 10.61/10.78  thf('11', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['9', '10'])).
% 10.61/10.78  thf('12', plain,
% 10.61/10.78      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 10.61/10.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.61/10.78  thf(d5_subset_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]:
% 10.61/10.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.61/10.78       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 10.61/10.78  thf('13', plain,
% 10.61/10.78      (![X25 : $i, X26 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 10.61/10.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.61/10.78  thf('14', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['12', '13'])).
% 10.61/10.78  thf(t39_xboole_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]:
% 10.61/10.78     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 10.61/10.78  thf('15', plain,
% 10.61/10.78      (![X7 : $i, X8 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 10.61/10.78           = (k2_xboole_0 @ X7 @ X8))),
% 10.61/10.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.61/10.78  thf('16', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ k1_xboole_0 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 10.61/10.78           = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['14', '15'])).
% 10.61/10.78  thf('17', plain,
% 10.61/10.78      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 10.61/10.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.61/10.78  thf(d2_subset_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]:
% 10.61/10.78     ( ( ( v1_xboole_0 @ A ) =>
% 10.61/10.78         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 10.61/10.78       ( ( ~( v1_xboole_0 @ A ) ) =>
% 10.61/10.78         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 10.61/10.78  thf('18', plain,
% 10.61/10.78      (![X22 : $i, X23 : $i]:
% 10.61/10.78         (~ (m1_subset_1 @ X22 @ X23)
% 10.61/10.78          | (r2_hidden @ X22 @ X23)
% 10.61/10.78          | (v1_xboole_0 @ X23))),
% 10.61/10.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.61/10.78  thf('19', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 10.61/10.78          | (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['17', '18'])).
% 10.61/10.78  thf(fc1_subset_1, axiom,
% 10.61/10.78    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 10.61/10.78  thf('20', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 10.61/10.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.61/10.78  thf('21', plain,
% 10.61/10.78      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.61/10.78      inference('clc', [status(thm)], ['19', '20'])).
% 10.61/10.78  thf(d1_zfmisc_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]:
% 10.61/10.78     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 10.61/10.78       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 10.61/10.78  thf('22', plain,
% 10.61/10.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 10.61/10.78         (~ (r2_hidden @ X20 @ X19)
% 10.61/10.78          | (r1_tarski @ X20 @ X18)
% 10.61/10.78          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.61/10.78  thf('23', plain,
% 10.61/10.78      (![X18 : $i, X20 : $i]:
% 10.61/10.78         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 10.61/10.78      inference('simplify', [status(thm)], ['22'])).
% 10.61/10.78  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 10.61/10.78      inference('sup-', [status(thm)], ['21', '23'])).
% 10.61/10.78  thf(t12_xboole_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]:
% 10.61/10.78     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 10.61/10.78  thf('25', plain,
% 10.61/10.78      (![X2 : $i, X3 : $i]:
% 10.61/10.78         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.61/10.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.61/10.78  thf('26', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['24', '25'])).
% 10.61/10.78  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['24', '25'])).
% 10.61/10.78  thf('28', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['16', '26', '27'])).
% 10.61/10.78  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['11', '28'])).
% 10.61/10.78  thf('30', plain,
% 10.61/10.78      (![X25 : $i, X26 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 10.61/10.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.61/10.78  thf('31', plain,
% 10.61/10.78      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['29', '30'])).
% 10.61/10.78  thf('32', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.61/10.78  thf(t41_xboole_1, axiom,
% 10.61/10.78    (![A:$i,B:$i,C:$i]:
% 10.61/10.78     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 10.61/10.78       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 10.61/10.78  thf('33', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('34', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 10.61/10.78           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['32', '33'])).
% 10.61/10.78  thf('35', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1)
% 10.61/10.78           = (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['31', '34'])).
% 10.61/10.78  thf('36', plain,
% 10.61/10.78      (![X35 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X35))),
% 10.61/10.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 10.61/10.78  thf(involutiveness_k3_subset_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]:
% 10.61/10.78     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 10.61/10.78       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 10.61/10.78  thf('37', plain,
% 10.61/10.78      (![X30 : $i, X31 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X31 @ (k3_subset_1 @ X31 @ X30)) = (X30))
% 10.61/10.78          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 10.61/10.78      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 10.61/10.78  thf('38', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['36', '37'])).
% 10.61/10.78  thf('39', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['16', '26', '27'])).
% 10.61/10.78  thf('40', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 10.61/10.78      inference('demod', [status(thm)], ['38', '39'])).
% 10.61/10.78  thf('41', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1)
% 10.61/10.78           = (k1_xboole_0))),
% 10.61/10.78      inference('demod', [status(thm)], ['35', '40'])).
% 10.61/10.78  thf('42', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.61/10.78  thf('43', plain,
% 10.61/10.78      (![X22 : $i, X23 : $i]:
% 10.61/10.78         (~ (m1_subset_1 @ X22 @ X23)
% 10.61/10.78          | (r2_hidden @ X22 @ X23)
% 10.61/10.78          | (v1_xboole_0 @ X23))),
% 10.61/10.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.61/10.78  thf('44', plain,
% 10.61/10.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 10.61/10.78        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['42', '43'])).
% 10.61/10.78  thf('45', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 10.61/10.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.61/10.78  thf('46', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('clc', [status(thm)], ['44', '45'])).
% 10.61/10.78  thf('47', plain,
% 10.61/10.78      (![X18 : $i, X20 : $i]:
% 10.61/10.78         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 10.61/10.78      inference('simplify', [status(thm)], ['22'])).
% 10.61/10.78  thf('48', plain, ((r1_tarski @ sk_B @ sk_A)),
% 10.61/10.78      inference('sup-', [status(thm)], ['46', '47'])).
% 10.61/10.78  thf('49', plain,
% 10.61/10.78      (![X2 : $i, X3 : $i]:
% 10.61/10.78         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.61/10.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.61/10.78  thf('50', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 10.61/10.78      inference('sup-', [status(thm)], ['48', '49'])).
% 10.61/10.78  thf('51', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('52', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 10.61/10.78           = (k4_xboole_0 @ X0 @ sk_A))),
% 10.61/10.78      inference('sup+', [status(thm)], ['50', '51'])).
% 10.61/10.78  thf('53', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.61/10.78  thf('54', plain,
% 10.61/10.78      (![X22 : $i, X23 : $i]:
% 10.61/10.78         (~ (m1_subset_1 @ X22 @ X23)
% 10.61/10.78          | (r2_hidden @ X22 @ X23)
% 10.61/10.78          | (v1_xboole_0 @ X23))),
% 10.61/10.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.61/10.78  thf('55', plain,
% 10.61/10.78      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 10.61/10.78        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['53', '54'])).
% 10.61/10.78  thf('56', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 10.61/10.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.61/10.78  thf('57', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('clc', [status(thm)], ['55', '56'])).
% 10.61/10.78  thf('58', plain,
% 10.61/10.78      (![X18 : $i, X20 : $i]:
% 10.61/10.78         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 10.61/10.78      inference('simplify', [status(thm)], ['22'])).
% 10.61/10.78  thf('59', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 10.61/10.78      inference('sup-', [status(thm)], ['57', '58'])).
% 10.61/10.78  thf(t34_xboole_1, axiom,
% 10.61/10.78    (![A:$i,B:$i,C:$i]:
% 10.61/10.78     ( ( r1_tarski @ A @ B ) =>
% 10.61/10.78       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 10.61/10.78  thf('60', plain,
% 10.61/10.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.61/10.78         (~ (r1_tarski @ X4 @ X5)
% 10.61/10.78          | (r1_tarski @ (k4_xboole_0 @ X6 @ X5) @ (k4_xboole_0 @ X6 @ X4)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t34_xboole_1])).
% 10.61/10.78  thf('61', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_A) @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 10.61/10.78      inference('sup-', [status(thm)], ['59', '60'])).
% 10.61/10.78  thf('62', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_A) @ 
% 10.61/10.78          (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_1))),
% 10.61/10.78      inference('sup+', [status(thm)], ['52', '61'])).
% 10.61/10.78  thf('63', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.61/10.78  thf('64', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.61/10.78  thf(t7_xboole_1, axiom,
% 10.61/10.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 10.61/10.78  thf('65', plain,
% 10.61/10.78      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 10.61/10.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 10.61/10.78  thf('66', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['64', '65'])).
% 10.61/10.78  thf('67', plain,
% 10.61/10.78      (![X2 : $i, X3 : $i]:
% 10.61/10.78         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.61/10.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.61/10.78  thf('68', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 10.61/10.78           = (k2_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['66', '67'])).
% 10.61/10.78  thf('69', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 10.61/10.78           = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('sup+', [status(thm)], ['63', '68'])).
% 10.61/10.78  thf('70', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('71', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X0 @ X1))
% 10.61/10.78           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['69', '70'])).
% 10.61/10.78  thf('72', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('73', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('74', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X0) @ X1)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['71', '72', '73'])).
% 10.61/10.78  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['24', '25'])).
% 10.61/10.78  thf('76', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 10.61/10.78           = (k2_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['66', '67'])).
% 10.61/10.78  thf('77', plain,
% 10.61/10.78      (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['75', '76'])).
% 10.61/10.78  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['24', '25'])).
% 10.61/10.78  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['77', '78'])).
% 10.61/10.78  thf('80', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('81', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 10.61/10.78           = (k4_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['79', '80'])).
% 10.61/10.78  thf('82', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['74', '81'])).
% 10.61/10.78  thf('83', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_A) @ 
% 10.61/10.78          (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_B))),
% 10.61/10.78      inference('demod', [status(thm)], ['62', '82'])).
% 10.61/10.78  thf('84', plain,
% 10.61/10.78      ((r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_1) @ sk_A) @ 
% 10.61/10.78        k1_xboole_0)),
% 10.61/10.78      inference('sup+', [status(thm)], ['41', '83'])).
% 10.61/10.78  thf('85', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.61/10.78  thf('86', plain,
% 10.61/10.78      ((r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 10.61/10.78        k1_xboole_0)),
% 10.61/10.78      inference('demod', [status(thm)], ['84', '85'])).
% 10.61/10.78  thf('87', plain,
% 10.61/10.78      (![X2 : $i, X3 : $i]:
% 10.61/10.78         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.61/10.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.61/10.78  thf('88', plain,
% 10.61/10.78      (((k2_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) @ 
% 10.61/10.78         k1_xboole_0) = (k1_xboole_0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['86', '87'])).
% 10.61/10.78  thf('89', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['24', '25'])).
% 10.61/10.78  thf('90', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.61/10.78  thf('91', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['89', '90'])).
% 10.61/10.78  thf('92', plain,
% 10.61/10.78      (((k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A) = (k1_xboole_0))),
% 10.61/10.78      inference('demod', [status(thm)], ['88', '91'])).
% 10.61/10.78  thf('93', plain,
% 10.61/10.78      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['29', '30'])).
% 10.61/10.78  thf('94', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 10.61/10.78           = (k2_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['66', '67'])).
% 10.61/10.78  thf('95', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('96', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k2_xboole_0 @ X1 @ X0))
% 10.61/10.78           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['94', '95'])).
% 10.61/10.78  thf('97', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('98', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('99', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1) @ X0)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['96', '97', '98'])).
% 10.61/10.78  thf('100', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ 
% 10.61/10.78           (k3_subset_1 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)) @ 
% 10.61/10.78           X0)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['93', '99'])).
% 10.61/10.78  thf('101', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 10.61/10.78      inference('demod', [status(thm)], ['38', '39'])).
% 10.61/10.78  thf('102', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['100', '101'])).
% 10.61/10.78  thf('103', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 10.61/10.78      inference('demod', [status(thm)], ['38', '39'])).
% 10.61/10.78  thf('104', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['12', '13'])).
% 10.61/10.78  thf('105', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['16', '26', '27'])).
% 10.61/10.78  thf('106', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 10.61/10.78      inference('demod', [status(thm)], ['104', '105'])).
% 10.61/10.78  thf('107', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((X1) = (k4_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['103', '106'])).
% 10.61/10.78  thf('108', plain,
% 10.61/10.78      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 10.61/10.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 10.61/10.78  thf('109', plain,
% 10.61/10.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.61/10.78         (~ (r1_tarski @ X4 @ X5)
% 10.61/10.78          | (r1_tarski @ (k4_xboole_0 @ X6 @ X5) @ (k4_xboole_0 @ X6 @ X4)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t34_xboole_1])).
% 10.61/10.78  thf('110', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 10.61/10.78          (k4_xboole_0 @ X2 @ X1))),
% 10.61/10.78      inference('sup-', [status(thm)], ['108', '109'])).
% 10.61/10.78  thf('111', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('112', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 10.61/10.78          (k4_xboole_0 @ X2 @ X1))),
% 10.61/10.78      inference('demod', [status(thm)], ['110', '111'])).
% 10.61/10.78  thf('113', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ 
% 10.61/10.78          (k4_xboole_0 @ X0 @ (k3_subset_1 @ X1 @ X1)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['107', '112'])).
% 10.61/10.78  thf('114', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((X1) = (k4_xboole_0 @ X1 @ (k3_subset_1 @ X0 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['103', '106'])).
% 10.61/10.78  thf('115', plain,
% 10.61/10.78      (![X0 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X0)),
% 10.61/10.78      inference('demod', [status(thm)], ['113', '114'])).
% 10.61/10.78  thf('116', plain,
% 10.61/10.78      (![X2 : $i, X3 : $i]:
% 10.61/10.78         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 10.61/10.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 10.61/10.78  thf('117', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['115', '116'])).
% 10.61/10.78  thf('118', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 10.61/10.78      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 10.61/10.78  thf('119', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)) = (X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['117', '118'])).
% 10.61/10.78  thf('120', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['24', '25'])).
% 10.61/10.78  thf('121', plain,
% 10.61/10.78      (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ k1_xboole_0 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['119', '120'])).
% 10.61/10.78  thf('122', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k1_xboole_0)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['102', '121'])).
% 10.61/10.78  thf('123', plain,
% 10.61/10.78      (![X0 : $i, X2 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X0)),
% 10.61/10.78      inference('demod', [status(thm)], ['113', '114'])).
% 10.61/10.78  thf('124', plain,
% 10.61/10.78      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.61/10.78         (~ (r1_tarski @ X17 @ X18)
% 10.61/10.78          | (r2_hidden @ X17 @ X19)
% 10.61/10.78          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 10.61/10.78  thf('125', plain,
% 10.61/10.78      (![X17 : $i, X18 : $i]:
% 10.61/10.78         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 10.61/10.78      inference('simplify', [status(thm)], ['124'])).
% 10.61/10.78  thf('126', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['123', '125'])).
% 10.61/10.78  thf('127', plain,
% 10.61/10.78      (![X22 : $i, X23 : $i]:
% 10.61/10.78         (~ (r2_hidden @ X22 @ X23)
% 10.61/10.78          | (m1_subset_1 @ X22 @ X23)
% 10.61/10.78          | (v1_xboole_0 @ X23))),
% 10.61/10.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.61/10.78  thf('128', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 10.61/10.78          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['126', '127'])).
% 10.61/10.78  thf('129', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 10.61/10.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.61/10.78  thf('130', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 10.61/10.78      inference('clc', [status(thm)], ['128', '129'])).
% 10.61/10.78  thf('131', plain,
% 10.61/10.78      (![X25 : $i, X26 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 10.61/10.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.61/10.78  thf('132', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 10.61/10.78           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['130', '131'])).
% 10.61/10.78  thf('133', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k1_xboole_0)
% 10.61/10.78           = (k4_xboole_0 @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['122', '132'])).
% 10.61/10.78  thf('134', plain,
% 10.61/10.78      (![X7 : $i, X8 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7))
% 10.61/10.78           = (k2_xboole_0 @ X7 @ X8))),
% 10.61/10.78      inference('cnf', [status(esa)], [t39_xboole_1])).
% 10.61/10.78  thf('135', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 10.61/10.78           = (k2_xboole_0 @ X0 @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 10.61/10.78      inference('sup+', [status(thm)], ['133', '134'])).
% 10.61/10.78  thf('136', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['89', '90'])).
% 10.61/10.78  thf('137', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((X0)
% 10.61/10.78           = (k2_xboole_0 @ X0 @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0))))),
% 10.61/10.78      inference('demod', [status(thm)], ['135', '136'])).
% 10.61/10.78  thf('138', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['64', '65'])).
% 10.61/10.78  thf('139', plain,
% 10.61/10.78      (![X17 : $i, X18 : $i]:
% 10.61/10.78         ((r2_hidden @ X17 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X17 @ X18))),
% 10.61/10.78      inference('simplify', [status(thm)], ['124'])).
% 10.61/10.78  thf('140', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['138', '139'])).
% 10.61/10.78  thf('141', plain,
% 10.61/10.78      (![X22 : $i, X23 : $i]:
% 10.61/10.78         (~ (r2_hidden @ X22 @ X23)
% 10.61/10.78          | (m1_subset_1 @ X22 @ X23)
% 10.61/10.78          | (v1_xboole_0 @ X23))),
% 10.61/10.78      inference('cnf', [status(esa)], [d2_subset_1])).
% 10.61/10.78  thf('142', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 10.61/10.78          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 10.61/10.78      inference('sup-', [status(thm)], ['140', '141'])).
% 10.61/10.78  thf('143', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 10.61/10.78      inference('cnf', [status(esa)], [fc1_subset_1])).
% 10.61/10.78  thf('144', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('clc', [status(thm)], ['142', '143'])).
% 10.61/10.78  thf('145', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]:
% 10.61/10.78         (m1_subset_1 @ (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 10.61/10.78          (k1_zfmisc_1 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['137', '144'])).
% 10.61/10.78  thf('146', plain,
% 10.61/10.78      ((m1_subset_1 @ 
% 10.61/10.78        (k3_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ k1_xboole_0) @ 
% 10.61/10.78        (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('sup+', [status(thm)], ['92', '145'])).
% 10.61/10.78  thf('147', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['16', '26', '27'])).
% 10.61/10.78  thf('148', plain,
% 10.61/10.78      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('demod', [status(thm)], ['146', '147'])).
% 10.61/10.78  thf('149', plain,
% 10.61/10.78      (![X25 : $i, X26 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 10.61/10.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.61/10.78  thf('150', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 10.61/10.78         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 10.61/10.78      inference('sup-', [status(thm)], ['148', '149'])).
% 10.61/10.78  thf('151', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 10.61/10.78           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 10.61/10.78      inference('sup+', [status(thm)], ['32', '33'])).
% 10.61/10.78  thf('152', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.61/10.78  thf('153', plain,
% 10.61/10.78      (![X25 : $i, X26 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 10.61/10.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.61/10.78  thf('154', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.61/10.78      inference('sup-', [status(thm)], ['152', '153'])).
% 10.61/10.78  thf('155', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 10.61/10.78         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 10.61/10.78      inference('demod', [status(thm)], ['150', '151', '154'])).
% 10.61/10.78  thf('156', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 10.61/10.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.61/10.78  thf('157', plain,
% 10.61/10.78      (![X25 : $i, X26 : $i]:
% 10.61/10.78         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 10.61/10.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 10.61/10.78      inference('cnf', [status(esa)], [d5_subset_1])).
% 10.61/10.78  thf('158', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 10.61/10.78      inference('sup-', [status(thm)], ['156', '157'])).
% 10.61/10.78  thf('159', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.61/10.78      inference('sup-', [status(thm)], ['152', '153'])).
% 10.61/10.78  thf('160', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['74', '81'])).
% 10.61/10.78  thf('161', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ X0)
% 10.61/10.78           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ sk_B))),
% 10.61/10.78      inference('sup+', [status(thm)], ['159', '160'])).
% 10.61/10.78  thf('162', plain,
% 10.61/10.78      (((k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1)
% 10.61/10.78         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))),
% 10.61/10.78      inference('sup+', [status(thm)], ['158', '161'])).
% 10.61/10.78  thf('163', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 10.61/10.78         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))),
% 10.61/10.78      inference('demod', [status(thm)], ['155', '162'])).
% 10.61/10.78  thf('164', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 10.61/10.78      inference('sup-', [status(thm)], ['152', '153'])).
% 10.61/10.78  thf('165', plain,
% 10.61/10.78      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 10.61/10.78      inference('sup-', [status(thm)], ['156', '157'])).
% 10.61/10.78  thf('166', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['64', '65'])).
% 10.61/10.78  thf('167', plain,
% 10.61/10.78      (![X4 : $i, X5 : $i, X6 : $i]:
% 10.61/10.78         (~ (r1_tarski @ X4 @ X5)
% 10.61/10.78          | (r1_tarski @ (k4_xboole_0 @ X6 @ X5) @ (k4_xboole_0 @ X6 @ X4)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t34_xboole_1])).
% 10.61/10.78  thf('168', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 10.61/10.78          (k4_xboole_0 @ X2 @ X0))),
% 10.61/10.78      inference('sup-', [status(thm)], ['166', '167'])).
% 10.61/10.78  thf('169', plain,
% 10.61/10.78      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.61/10.78         ((k4_xboole_0 @ (k4_xboole_0 @ X9 @ X10) @ X11)
% 10.61/10.78           = (k4_xboole_0 @ X9 @ (k2_xboole_0 @ X10 @ X11)))),
% 10.61/10.78      inference('cnf', [status(esa)], [t41_xboole_1])).
% 10.61/10.78  thf('170', plain,
% 10.61/10.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0) @ 
% 10.61/10.78          (k4_xboole_0 @ X2 @ X0))),
% 10.61/10.78      inference('demod', [status(thm)], ['168', '169'])).
% 10.61/10.78  thf('171', plain,
% 10.61/10.78      (![X0 : $i]:
% 10.61/10.78         (r1_tarski @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0) @ 
% 10.61/10.78          (k4_xboole_0 @ sk_A @ X0))),
% 10.61/10.78      inference('sup+', [status(thm)], ['165', '170'])).
% 10.61/10.78  thf('172', plain,
% 10.61/10.78      ((r1_tarski @ (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B) @ 
% 10.61/10.78        (k3_subset_1 @ sk_A @ sk_B))),
% 10.61/10.78      inference('sup+', [status(thm)], ['164', '171'])).
% 10.61/10.78  thf('173', plain, ($false),
% 10.61/10.78      inference('demod', [status(thm)], ['8', '163', '172'])).
% 10.61/10.78  
% 10.61/10.78  % SZS output end Refutation
% 10.61/10.78  
% 10.61/10.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
