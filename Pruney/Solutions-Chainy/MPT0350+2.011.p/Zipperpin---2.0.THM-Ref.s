%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SpWoJCb0gX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 188 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   11
%              Number of atoms          :  567 (1359 expanded)
%              Number of equality atoms :   54 ( 114 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_tarski @ X22 @ X20 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = X6 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( m1_subset_1 @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) )
      | ( ( k4_subset_1 @ X34 @ X33 @ X35 )
        = ( k2_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['13','25'])).

thf('27',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ X11 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = ( k2_xboole_0 @ ( k5_xboole_0 @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) )
      = ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ ( k3_xboole_0 @ X4 @ X5 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('44',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('46',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','37','44','45'])).

thf('47',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
    = sk_A ),
    inference(demod,[status(thm)],['26','27','46'])).

thf('48',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('49',plain,(
    ! [X29: $i] :
      ( ( k2_subset_1 @ X29 )
      = X29 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('50',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf('52',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('54',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SpWoJCb0gX
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 293 iterations in 0.081s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.54  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(t25_subset_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.54         ( k2_subset_1 @ A ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i]:
% 0.21/0.54        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 0.21/0.54            ( k2_subset_1 @ A ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 0.21/0.54  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d2_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.54       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X26 @ X27)
% 0.21/0.54          | (r2_hidden @ X26 @ X27)
% 0.21/0.54          | (v1_xboole_0 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.54        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(fc1_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('3', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.54  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.54  thf(d1_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X22 @ X21)
% 0.21/0.54          | (r1_tarski @ X22 @ X20)
% 0.21/0.54          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X20 : $i, X22 : $i]:
% 0.21/0.54         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.54  thf('7', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.54      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.54  thf(t28_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X6 : $i, X7 : $i]:
% 0.21/0.54         (((k3_xboole_0 @ X6 @ X7) = (X6)) | ~ (r1_tarski @ X6 @ X7))),
% 0.21/0.54      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.54  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.54  thf('10', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.54  thf(t100_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.54           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k4_xboole_0 @ X0 @ X1)
% 0.21/0.54           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.54  thf(t36_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 0.21/0.54      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (r1_tarski @ X19 @ X20)
% 0.21/0.54          | (r2_hidden @ X19 @ X21)
% 0.21/0.54          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X19 : $i, X20 : $i]:
% 0.21/0.54         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 0.21/0.54      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.54  thf('17', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X26 @ X27)
% 0.21/0.54          | (m1_subset_1 @ X26 @ X27)
% 0.21/0.54          | (v1_xboole_0 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.21/0.54          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.21/0.54      inference('clc', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k4_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.21/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.54       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.21/0.54  thf('23', plain,
% 0.21/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.21/0.54          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34))
% 0.21/0.54          | ((k4_subset_1 @ X34 @ X33 @ X35) = (k2_xboole_0 @ X33 @ X35)))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 0.21/0.54          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 0.21/0.54           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B))
% 0.21/0.54         = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['13', '25'])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.54  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.54  thf(t93_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k2_xboole_0 @ A @ B ) =
% 0.21/0.54       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X10 @ X11)
% 0.21/0.54           = (k2_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.21/0.54              (k3_xboole_0 @ X10 @ X11)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t93_xboole_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X0 @ X1)
% 0.21/0.54           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.54      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (((k2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.54         = (k2_xboole_0 @ (k5_xboole_0 @ sk_A @ sk_B) @ sk_B))),
% 0.21/0.54      inference('sup+', [status(thm)], ['28', '31'])).
% 0.21/0.54  thf(commutativity_k2_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      (![X12 : $i, X13 : $i]:
% 0.21/0.54         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.54  thf(l51_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('34', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.54  thf('36', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         ((k3_tarski @ (k2_tarski @ X24 @ X25)) = (k2_xboole_0 @ X24 @ X25))),
% 0.21/0.54      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.54  thf(t22_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X4 @ (k3_xboole_0 @ X4 @ X5)) = (X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['39', '40'])).
% 0.21/0.54  thf('42', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.54      inference('sup+', [status(thm)], ['38', '41'])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('44', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.54  thf('45', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (((sk_A) = (k2_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.54      inference('demod', [status(thm)], ['32', '37', '44', '45'])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) = (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['26', '27', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.54         != (k2_subset_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.21/0.54  thf('49', plain, (![X29 : $i]: ((k2_subset_1 @ X29) = (X29))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.21/0.54  thf('51', plain,
% 0.21/0.54      (((k4_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup+', [status(thm)], ['9', '12'])).
% 0.21/0.54  thf('52', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(d5_subset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.54       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.54  thf('53', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i]:
% 0.21/0.54         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 0.21/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.54  thf('54', plain,
% 0.21/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      (((k3_subset_1 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.54      inference('sup+', [status(thm)], ['51', '54'])).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (((k4_subset_1 @ sk_A @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '55'])).
% 0.21/0.54  thf('57', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['47', '56'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
