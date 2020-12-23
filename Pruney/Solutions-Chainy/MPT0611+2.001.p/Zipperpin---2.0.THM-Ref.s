%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3yExTdkae

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 182 expanded)
%              Number of leaves         :   31 (  70 expanded)
%              Depth                    :   19
%              Number of atoms          :  521 (1199 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('3',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t27_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X56: $i,X57: $i] :
      ( ~ ( v1_relat_1 @ X56 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X57 @ X56 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X57 ) @ ( k2_relat_1 @ X56 ) ) )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t27_relat_1])).

thf('7',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X13 ) @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,
    ( ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','19'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('21',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X37 ) @ X38 )
      | ( ( k8_relat_1 @ X38 @ X37 )
        = X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
      | ( ( k8_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
        = ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t62_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X59: $i] :
      ( ( ( k5_relat_1 @ k1_xboole_0 @ X59 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X59 ) ) ),
    inference(cnf,[status(esa)],[t62_relat_1])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k8_relat_1 @ X36 @ X35 )
        = ( k5_relat_1 @ X35 @ ( k6_relat_1 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X30: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('27',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','29'])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X33 @ X34 ) ) @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','28'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_xboole_0 @ X7 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X1 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
      | ( ( k8_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
        = ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['22','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_A )
      | ( ( k8_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
        = ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) )
      = ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X42: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X42 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf('48',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('53',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_A @ sk_B_2 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['0','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3yExTdkae
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 164 iterations in 0.071s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.53  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.53  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.53  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(t215_relat_1, conjecture,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.53             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i]:
% 0.21/0.53        ( ( v1_relat_1 @ A ) =>
% 0.21/0.53          ( ![B:$i]:
% 0.21/0.53            ( ( v1_relat_1 @ B ) =>
% 0.21/0.53              ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.53                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t215_relat_1])).
% 0.21/0.53  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B_2)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(fc1_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X31 : $i, X32 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X31) | (v1_relat_1 @ (k3_xboole_0 @ X31 @ X32)))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X31 : $i, X32 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X31) | (v1_relat_1 @ (k3_xboole_0 @ X31 @ X32)))),
% 0.21/0.53      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      ((r1_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(d7_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (((k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B_2))
% 0.21/0.53         = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.53  thf(t27_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ( v1_relat_1 @ B ) =>
% 0.21/0.53           ( r1_tarski @
% 0.21/0.53             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.21/0.53             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X56 : $i, X57 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ X56)
% 0.21/0.53          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X57 @ X56)) @ 
% 0.21/0.53             (k3_xboole_0 @ (k2_relat_1 @ X57) @ (k2_relat_1 @ X56)))
% 0.21/0.53          | ~ (v1_relat_1 @ X57))),
% 0.21/0.53      inference('cnf', [status(esa)], [t27_relat_1])).
% 0.21/0.53  thf('7', plain,
% 0.21/0.53      (((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ k1_xboole_0)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_A)
% 0.21/0.53        | ~ (v1_relat_1 @ sk_B_2))),
% 0.21/0.53      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.53  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('9', plain, ((v1_relat_1 @ sk_B_2)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.53  thf('11', plain,
% 0.21/0.53      ((r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ k1_xboole_0)),
% 0.21/0.53      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.21/0.53  thf(t67_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.53         ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.53       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (((X8) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X8 @ X9)
% 0.21/0.53          | ~ (r1_tarski @ X8 @ X10)
% 0.21/0.53          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ X0)
% 0.21/0.53          | ((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.53  thf(t3_xboole_0, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.53            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.53       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.53            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.53  thf('14', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.21/0.53      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('15', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(l24_zfmisc_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.53  thf('16', plain,
% 0.21/0.53      (![X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X13) @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.21/0.53      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.21/0.53  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['14', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) @ X0)
% 0.21/0.53          | ((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '18'])).
% 0.21/0.53  thf('20', plain,
% 0.21/0.53      (((k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.53  thf(t125_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.21/0.53         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.21/0.53  thf('21', plain,
% 0.21/0.53      (![X37 : $i, X38 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k2_relat_1 @ X37) @ X38)
% 0.21/0.53          | ((k8_relat_1 @ X38 @ X37) = (X37))
% 0.21/0.53          | ~ (v1_relat_1 @ X37))),
% 0.21/0.53      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 0.21/0.53          | ((k8_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 0.21/0.53              = (k3_xboole_0 @ sk_A @ sk_B_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.53  thf(t62_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.21/0.53         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X59 : $i]:
% 0.21/0.53         (((k5_relat_1 @ k1_xboole_0 @ X59) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X59))),
% 0.21/0.53      inference('cnf', [status(esa)], [t62_relat_1])).
% 0.21/0.53  thf(t123_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X35 : $i, X36 : $i]:
% 0.21/0.53         (((k8_relat_1 @ X36 @ X35) = (k5_relat_1 @ X35 @ (k6_relat_1 @ X36)))
% 0.21/0.53          | ~ (v1_relat_1 @ X35))),
% 0.21/0.53      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.53  thf('25', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.21/0.53  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.53  thf('26', plain, (![X30 : $i]: (v1_relat_1 @ (k6_relat_1 @ X30))),
% 0.21/0.53      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.53  thf(d1_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) <=>
% 0.21/0.53       ( ![B:$i]:
% 0.21/0.53         ( ~( ( r2_hidden @ B @ A ) & 
% 0.21/0.53              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (![X26 : $i]: ((v1_relat_1 @ X26) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.21/0.53      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.21/0.53  thf('28', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.53  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i]: ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['25', '26', '29'])).
% 0.21/0.53  thf(t116_relat_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ B ) =>
% 0.21/0.53       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X33 : $i, X34 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X33 @ X34)) @ X33)
% 0.21/0.53          | ~ (v1_relat_1 @ X34))),
% 0.21/0.53      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 0.21/0.53          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.53      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.53  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('34', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain, (![X7 : $i]: (r1_xboole_0 @ X7 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf('36', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.53         (((X8) = (k1_xboole_0))
% 0.21/0.53          | ~ (r1_tarski @ X8 @ X9)
% 0.21/0.53          | ~ (r1_tarski @ X8 @ X10)
% 0.21/0.53          | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.21/0.53      inference('cnf', [status(esa)], [t67_xboole_1])).
% 0.21/0.53  thf('38', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X1)
% 0.21/0.53          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.53  thf('39', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('40', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.53          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.53  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['35', '40'])).
% 0.21/0.53  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '41'])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 0.21/0.53          | ((k8_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 0.21/0.53              = (k3_xboole_0 @ sk_A @ sk_B_2)))),
% 0.21/0.53      inference('demod', [status(thm)], ['22', '42'])).
% 0.21/0.53  thf('44', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (v1_relat_1 @ sk_A)
% 0.21/0.53          | ((k8_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 0.21/0.53              = (k3_xboole_0 @ sk_A @ sk_B_2)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['2', '43'])).
% 0.21/0.53  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('46', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         ((k8_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B_2))
% 0.21/0.53           = (k3_xboole_0 @ sk_A @ sk_B_2))),
% 0.21/0.53      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.53  thf(t137_relat_1, axiom,
% 0.21/0.53    (![A:$i]:
% 0.21/0.53     ( ( v1_relat_1 @ A ) =>
% 0.21/0.53       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.53  thf('47', plain,
% 0.21/0.53      (![X42 : $i]:
% 0.21/0.53         (((k8_relat_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))
% 0.21/0.53          | ~ (v1_relat_1 @ X42))),
% 0.21/0.53      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.21/0.53  thf('48', plain,
% 0.21/0.53      ((((k3_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.53        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B_2)))),
% 0.21/0.53      inference('sup+', [status(thm)], ['46', '47'])).
% 0.21/0.53  thf('49', plain,
% 0.21/0.53      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '48'])).
% 0.21/0.53  thf('50', plain, ((v1_relat_1 @ sk_A)),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('51', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.21/0.53      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.53  thf('52', plain,
% 0.21/0.53      (![X0 : $i, X2 : $i]:
% 0.21/0.53         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.53  thf('53', plain,
% 0.21/0.53      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B_2))),
% 0.21/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.53  thf('54', plain, ((r1_xboole_0 @ sk_A @ sk_B_2)),
% 0.21/0.53      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.53  thf('55', plain, ($false), inference('demod', [status(thm)], ['0', '54'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
