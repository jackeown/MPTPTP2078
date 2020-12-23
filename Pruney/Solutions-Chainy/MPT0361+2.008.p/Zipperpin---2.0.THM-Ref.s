%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cUNPr7uk6E

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:51 EST 2020

% Result     : Theorem 7.24s
% Output     : Refutation 7.24s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 191 expanded)
%              Number of leaves         :   28 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          :  867 (1438 expanded)
%              Number of equality atoms :   63 (  89 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = ( k3_subset_1 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X32 @ ( k3_subset_1 @ X32 @ X31 ) )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('48',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('50',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('53',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','55'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('57',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('58',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('67',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('69',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('71',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['62','73'])).

thf('75',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('76',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('82',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r2_hidden @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X30: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('90',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('92',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('94',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X14 )
      = ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('98',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['92','95','98'])).

thf('100',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('101',plain,(
    $false ),
    inference(demod,[status(thm)],['8','99','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cUNPr7uk6E
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:03:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.24/7.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.24/7.45  % Solved by: fo/fo7.sh
% 7.24/7.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.24/7.45  % done 9681 iterations in 6.992s
% 7.24/7.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.24/7.45  % SZS output start Refutation
% 7.24/7.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.24/7.45  thf(sk_B_type, type, sk_B: $i).
% 7.24/7.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 7.24/7.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.24/7.45  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 7.24/7.45  thf(sk_C_1_type, type, sk_C_1: $i).
% 7.24/7.45  thf(sk_A_type, type, sk_A: $i).
% 7.24/7.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.24/7.45  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.24/7.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.24/7.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.24/7.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.24/7.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.24/7.45  thf(t41_subset_1, conjecture,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.45       ( ![C:$i]:
% 7.24/7.45         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.45           ( r1_tarski @
% 7.24/7.45             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 7.24/7.45             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 7.24/7.45  thf(zf_stmt_0, negated_conjecture,
% 7.24/7.45    (~( ![A:$i,B:$i]:
% 7.24/7.45        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.45          ( ![C:$i]:
% 7.24/7.45            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.45              ( r1_tarski @
% 7.24/7.45                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 7.24/7.45                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 7.24/7.45    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 7.24/7.45  thf('0', plain,
% 7.24/7.45      (~ (r1_tarski @ 
% 7.24/7.45          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 7.24/7.45          (k3_subset_1 @ sk_A @ sk_B))),
% 7.24/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.45  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.45  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.45  thf(redefinition_k4_subset_1, axiom,
% 7.24/7.45    (![A:$i,B:$i,C:$i]:
% 7.24/7.45     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 7.24/7.45         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.24/7.45       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 7.24/7.45  thf('3', plain,
% 7.24/7.45      (![X33 : $i, X34 : $i, X35 : $i]:
% 7.24/7.45         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 7.24/7.45          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 7.24/7.45          | ((k4_subset_1 @ X34 @ X33 @ X35) = (k2_xboole_0 @ X33 @ X35)))),
% 7.24/7.45      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 7.24/7.45  thf('4', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 7.24/7.45          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['2', '3'])).
% 7.24/7.45  thf('5', plain,
% 7.24/7.45      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 7.24/7.45      inference('sup-', [status(thm)], ['1', '4'])).
% 7.24/7.45  thf(commutativity_k2_xboole_0, axiom,
% 7.24/7.45    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 7.24/7.45  thf('6', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.24/7.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.24/7.45  thf('7', plain,
% 7.24/7.45      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 7.24/7.45      inference('demod', [status(thm)], ['5', '6'])).
% 7.24/7.45  thf('8', plain,
% 7.24/7.45      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 7.24/7.45          (k3_subset_1 @ sk_A @ sk_B))),
% 7.24/7.45      inference('demod', [status(thm)], ['0', '7'])).
% 7.24/7.45  thf(d10_xboole_0, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.24/7.45  thf('9', plain,
% 7.24/7.45      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.45  thf('10', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 7.24/7.45      inference('simplify', [status(thm)], ['9'])).
% 7.24/7.45  thf(d1_zfmisc_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 7.24/7.45       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 7.24/7.45  thf('11', plain,
% 7.24/7.45      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.24/7.45         (~ (r1_tarski @ X20 @ X21)
% 7.24/7.45          | (r2_hidden @ X20 @ X22)
% 7.24/7.45          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 7.24/7.45  thf('12', plain,
% 7.24/7.45      (![X20 : $i, X21 : $i]:
% 7.24/7.45         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 7.24/7.45      inference('simplify', [status(thm)], ['11'])).
% 7.24/7.45  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['10', '12'])).
% 7.24/7.45  thf(d2_subset_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( ( v1_xboole_0 @ A ) =>
% 7.24/7.45         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 7.24/7.45       ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.24/7.45         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 7.24/7.45  thf('14', plain,
% 7.24/7.45      (![X25 : $i, X26 : $i]:
% 7.24/7.45         (~ (r2_hidden @ X25 @ X26)
% 7.24/7.45          | (m1_subset_1 @ X25 @ X26)
% 7.24/7.45          | (v1_xboole_0 @ X26))),
% 7.24/7.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.24/7.45  thf('15', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 7.24/7.45          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['13', '14'])).
% 7.24/7.45  thf(fc1_subset_1, axiom,
% 7.24/7.45    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 7.24/7.45  thf('16', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 7.24/7.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.24/7.45  thf('17', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.45      inference('clc', [status(thm)], ['15', '16'])).
% 7.24/7.45  thf(d5_subset_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.45       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 7.24/7.45  thf('18', plain,
% 7.24/7.45      (![X28 : $i, X29 : $i]:
% 7.24/7.45         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 7.24/7.45          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.24/7.45  thf('19', plain,
% 7.24/7.45      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['17', '18'])).
% 7.24/7.45  thf(t41_xboole_1, axiom,
% 7.24/7.45    (![A:$i,B:$i,C:$i]:
% 7.24/7.45     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 7.24/7.45       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 7.24/7.45  thf('20', plain,
% 7.24/7.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.24/7.45           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.24/7.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.24/7.45  thf('21', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 7.24/7.45           = (k3_subset_1 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 7.24/7.45      inference('sup+', [status(thm)], ['19', '20'])).
% 7.24/7.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.24/7.45  thf('22', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 7.24/7.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.24/7.45  thf('23', plain,
% 7.24/7.45      (![X20 : $i, X21 : $i]:
% 7.24/7.45         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 7.24/7.45      inference('simplify', [status(thm)], ['11'])).
% 7.24/7.45  thf('24', plain,
% 7.24/7.45      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['22', '23'])).
% 7.24/7.45  thf('25', plain,
% 7.24/7.45      (![X25 : $i, X26 : $i]:
% 7.24/7.45         (~ (r2_hidden @ X25 @ X26)
% 7.24/7.45          | (m1_subset_1 @ X25 @ X26)
% 7.24/7.45          | (v1_xboole_0 @ X26))),
% 7.24/7.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.24/7.45  thf('26', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 7.24/7.45          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['24', '25'])).
% 7.24/7.45  thf('27', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 7.24/7.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.24/7.45  thf('28', plain,
% 7.24/7.45      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.45      inference('clc', [status(thm)], ['26', '27'])).
% 7.24/7.45  thf(involutiveness_k3_subset_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 7.24/7.45       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 7.24/7.45  thf('29', plain,
% 7.24/7.45      (![X31 : $i, X32 : $i]:
% 7.24/7.45         (((k3_subset_1 @ X32 @ (k3_subset_1 @ X32 @ X31)) = (X31))
% 7.24/7.45          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X32)))),
% 7.24/7.45      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 7.24/7.45  thf('30', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['28', '29'])).
% 7.24/7.45  thf('31', plain,
% 7.24/7.45      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 7.24/7.45      inference('clc', [status(thm)], ['26', '27'])).
% 7.24/7.45  thf('32', plain,
% 7.24/7.45      (![X28 : $i, X29 : $i]:
% 7.24/7.45         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 7.24/7.45          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.24/7.45  thf('33', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['31', '32'])).
% 7.24/7.45  thf(t39_xboole_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 7.24/7.45  thf('34', plain,
% 7.24/7.45      (![X10 : $i, X11 : $i]:
% 7.24/7.45         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 7.24/7.45           = (k2_xboole_0 @ X10 @ X11))),
% 7.24/7.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 7.24/7.45  thf('35', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 7.24/7.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.24/7.45  thf(t12_xboole_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]:
% 7.24/7.45     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 7.24/7.45  thf('36', plain,
% 7.24/7.45      (![X5 : $i, X6 : $i]:
% 7.24/7.45         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.24/7.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.24/7.45  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['35', '36'])).
% 7.24/7.45  thf('38', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 7.24/7.45      inference('sup+', [status(thm)], ['34', '37'])).
% 7.24/7.45  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['35', '36'])).
% 7.24/7.45  thf('40', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.24/7.45      inference('sup+', [status(thm)], ['38', '39'])).
% 7.24/7.45  thf('41', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 7.24/7.45      inference('sup+', [status(thm)], ['33', '40'])).
% 7.24/7.45  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 7.24/7.45      inference('demod', [status(thm)], ['30', '41'])).
% 7.24/7.45  thf('43', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 7.24/7.45           = (k1_xboole_0))),
% 7.24/7.45      inference('demod', [status(thm)], ['21', '42'])).
% 7.24/7.45  thf('44', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.45  thf('45', plain,
% 7.24/7.45      (![X25 : $i, X26 : $i]:
% 7.24/7.45         (~ (m1_subset_1 @ X25 @ X26)
% 7.24/7.45          | (r2_hidden @ X25 @ X26)
% 7.24/7.45          | (v1_xboole_0 @ X26))),
% 7.24/7.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.24/7.45  thf('46', plain,
% 7.24/7.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.24/7.45        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['44', '45'])).
% 7.24/7.45  thf('47', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 7.24/7.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.24/7.45  thf('48', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('clc', [status(thm)], ['46', '47'])).
% 7.24/7.45  thf('49', plain,
% 7.24/7.45      (![X21 : $i, X22 : $i, X23 : $i]:
% 7.24/7.45         (~ (r2_hidden @ X23 @ X22)
% 7.24/7.45          | (r1_tarski @ X23 @ X21)
% 7.24/7.45          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 7.24/7.45  thf('50', plain,
% 7.24/7.45      (![X21 : $i, X23 : $i]:
% 7.24/7.45         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 7.24/7.45      inference('simplify', [status(thm)], ['49'])).
% 7.24/7.45  thf('51', plain, ((r1_tarski @ sk_B @ sk_A)),
% 7.24/7.45      inference('sup-', [status(thm)], ['48', '50'])).
% 7.24/7.45  thf('52', plain,
% 7.24/7.45      (![X5 : $i, X6 : $i]:
% 7.24/7.45         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.24/7.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.24/7.45  thf('53', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 7.24/7.45      inference('sup-', [status(thm)], ['51', '52'])).
% 7.24/7.45  thf('54', plain,
% 7.24/7.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.24/7.45           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.24/7.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.24/7.45  thf('55', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 7.24/7.45           = (k4_xboole_0 @ X0 @ sk_A))),
% 7.24/7.45      inference('sup+', [status(thm)], ['53', '54'])).
% 7.24/7.45  thf('56', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ k1_xboole_0 @ sk_A)
% 7.24/7.45           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 7.24/7.45              sk_A))),
% 7.24/7.45      inference('sup+', [status(thm)], ['43', '55'])).
% 7.24/7.45  thf(t36_xboole_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 7.24/7.45  thf('57', plain,
% 7.24/7.45      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 7.24/7.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.24/7.45  thf('58', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 7.24/7.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.24/7.45  thf('59', plain,
% 7.24/7.45      (![X2 : $i, X4 : $i]:
% 7.24/7.45         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 7.24/7.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 7.24/7.45  thf('60', plain,
% 7.24/7.45      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['58', '59'])).
% 7.24/7.45  thf('61', plain,
% 7.24/7.45      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['57', '60'])).
% 7.24/7.45  thf('62', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k1_xboole_0)
% 7.24/7.45           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 7.24/7.45              sk_A))),
% 7.24/7.45      inference('demod', [status(thm)], ['56', '61'])).
% 7.24/7.45  thf('63', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.45  thf('64', plain,
% 7.24/7.45      (![X25 : $i, X26 : $i]:
% 7.24/7.45         (~ (m1_subset_1 @ X25 @ X26)
% 7.24/7.45          | (r2_hidden @ X25 @ X26)
% 7.24/7.45          | (v1_xboole_0 @ X26))),
% 7.24/7.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.24/7.45  thf('65', plain,
% 7.24/7.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.24/7.45        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['63', '64'])).
% 7.24/7.45  thf('66', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 7.24/7.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.24/7.45  thf('67', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('clc', [status(thm)], ['65', '66'])).
% 7.24/7.45  thf('68', plain,
% 7.24/7.45      (![X21 : $i, X23 : $i]:
% 7.24/7.45         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 7.24/7.45      inference('simplify', [status(thm)], ['49'])).
% 7.24/7.45  thf('69', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 7.24/7.45      inference('sup-', [status(thm)], ['67', '68'])).
% 7.24/7.45  thf('70', plain,
% 7.24/7.45      (![X5 : $i, X6 : $i]:
% 7.24/7.45         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 7.24/7.45      inference('cnf', [status(esa)], [t12_xboole_1])).
% 7.24/7.45  thf('71', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 7.24/7.45      inference('sup-', [status(thm)], ['69', '70'])).
% 7.24/7.45  thf('72', plain,
% 7.24/7.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.24/7.45           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.24/7.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.24/7.45  thf('73', plain,
% 7.24/7.45      (![X0 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_A)
% 7.24/7.45           = (k4_xboole_0 @ X0 @ sk_A))),
% 7.24/7.45      inference('sup+', [status(thm)], ['71', '72'])).
% 7.24/7.45  thf('74', plain,
% 7.24/7.45      (((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A))),
% 7.24/7.45      inference('sup+', [status(thm)], ['62', '73'])).
% 7.24/7.45  thf('75', plain,
% 7.24/7.45      (![X10 : $i, X11 : $i]:
% 7.24/7.45         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 7.24/7.45           = (k2_xboole_0 @ X10 @ X11))),
% 7.24/7.45      inference('cnf', [status(esa)], [t39_xboole_1])).
% 7.24/7.45  thf('76', plain,
% 7.24/7.45      (((k2_xboole_0 @ sk_A @ k1_xboole_0)
% 7.24/7.45         = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 7.24/7.45      inference('sup+', [status(thm)], ['74', '75'])).
% 7.24/7.45  thf('77', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.24/7.45      inference('sup-', [status(thm)], ['35', '36'])).
% 7.24/7.45  thf('78', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.24/7.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.24/7.45  thf('79', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 7.24/7.45      inference('sup+', [status(thm)], ['77', '78'])).
% 7.24/7.45  thf('80', plain,
% 7.24/7.45      (((sk_A) = (k2_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 7.24/7.45      inference('demod', [status(thm)], ['76', '79'])).
% 7.24/7.45  thf('81', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.24/7.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.24/7.45  thf(t7_xboole_1, axiom,
% 7.24/7.45    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 7.24/7.45  thf('82', plain,
% 7.24/7.45      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 7.24/7.45      inference('cnf', [status(esa)], [t7_xboole_1])).
% 7.24/7.45  thf('83', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 7.24/7.45      inference('sup+', [status(thm)], ['81', '82'])).
% 7.24/7.45  thf('84', plain,
% 7.24/7.45      (![X20 : $i, X21 : $i]:
% 7.24/7.45         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 7.24/7.45      inference('simplify', [status(thm)], ['11'])).
% 7.24/7.45  thf('85', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]:
% 7.24/7.45         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['83', '84'])).
% 7.24/7.45  thf('86', plain,
% 7.24/7.45      ((r2_hidden @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('sup+', [status(thm)], ['80', '85'])).
% 7.24/7.45  thf('87', plain,
% 7.24/7.45      (![X25 : $i, X26 : $i]:
% 7.24/7.45         (~ (r2_hidden @ X25 @ X26)
% 7.24/7.45          | (m1_subset_1 @ X25 @ X26)
% 7.24/7.45          | (v1_xboole_0 @ X26))),
% 7.24/7.45      inference('cnf', [status(esa)], [d2_subset_1])).
% 7.24/7.45  thf('88', plain,
% 7.24/7.45      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 7.24/7.45        | (m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['86', '87'])).
% 7.24/7.45  thf('89', plain, (![X30 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X30))),
% 7.24/7.45      inference('cnf', [status(esa)], [fc1_subset_1])).
% 7.24/7.45  thf('90', plain,
% 7.24/7.45      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('clc', [status(thm)], ['88', '89'])).
% 7.24/7.45  thf('91', plain,
% 7.24/7.45      (![X28 : $i, X29 : $i]:
% 7.24/7.45         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 7.24/7.45          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.24/7.45  thf('92', plain,
% 7.24/7.45      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 7.24/7.45         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 7.24/7.45      inference('sup-', [status(thm)], ['90', '91'])).
% 7.24/7.45  thf('93', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.24/7.45      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.24/7.45  thf('94', plain,
% 7.24/7.45      (![X12 : $i, X13 : $i, X14 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X14)
% 7.24/7.45           = (k4_xboole_0 @ X12 @ (k2_xboole_0 @ X13 @ X14)))),
% 7.24/7.45      inference('cnf', [status(esa)], [t41_xboole_1])).
% 7.24/7.45  thf('95', plain,
% 7.24/7.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.24/7.45         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 7.24/7.45           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 7.24/7.45      inference('sup+', [status(thm)], ['93', '94'])).
% 7.24/7.45  thf('96', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 7.24/7.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.24/7.45  thf('97', plain,
% 7.24/7.45      (![X28 : $i, X29 : $i]:
% 7.24/7.45         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 7.24/7.45          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 7.24/7.45      inference('cnf', [status(esa)], [d5_subset_1])).
% 7.24/7.45  thf('98', plain,
% 7.24/7.45      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 7.24/7.45      inference('sup-', [status(thm)], ['96', '97'])).
% 7.24/7.45  thf('99', plain,
% 7.24/7.45      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 7.24/7.45         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 7.24/7.45      inference('demod', [status(thm)], ['92', '95', '98'])).
% 7.24/7.45  thf('100', plain,
% 7.24/7.45      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 7.24/7.45      inference('cnf', [status(esa)], [t36_xboole_1])).
% 7.24/7.45  thf('101', plain, ($false),
% 7.24/7.45      inference('demod', [status(thm)], ['8', '99', '100'])).
% 7.24/7.45  
% 7.24/7.45  % SZS output end Refutation
% 7.24/7.45  
% 7.24/7.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
