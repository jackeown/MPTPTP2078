%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1BjEYKvEcm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:18 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 301 expanded)
%              Number of leaves         :   27 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  602 (2307 expanded)
%              Number of equality atoms :   45 ( 199 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t51_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
          = ( k1_tarski @ B ) )
       => ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t51_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('1',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( X41 != X40 )
      | ( r2_hidden @ X41 @ X42 )
      | ( X42
       != ( k2_tarski @ X43 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('2',plain,(
    ! [X40: $i,X43: $i] :
      ( r2_hidden @ X40 @ ( k2_tarski @ X43 @ X40 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X39: $i] :
      ( ( k5_xboole_0 @ X39 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

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

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X31: $i] :
      ( ( r1_xboole_0 @ X31 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('9',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ X36 @ X37 )
        = X36 )
      | ~ ( r1_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ X36 @ X37 )
        = X36 )
      | ~ ( r1_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['6','18'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X1 ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X2 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X39: $i] :
      ( ( k5_xboole_0 @ X39 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X27: $i] :
      ( ( k3_xboole_0 @ X27 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['22','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( r1_xboole_0 @ X33 @ ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( r1_xboole_0 @ X34 @ ( k4_xboole_0 @ X33 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X39: $i] :
      ( ( k5_xboole_0 @ X39 @ X39 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('40',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ~ ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','41'])).

thf('43',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('46',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ ( k4_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('49',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X28 @ ( k4_xboole_0 @ X29 @ X30 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X28 @ X29 ) @ ( k3_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('51',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k3_xboole_0 @ X14 @ X17 ) )
      | ~ ( r1_xboole_0 @ X14 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) )
      | ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) )
      | ~ ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','38'])).

thf('55',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['44','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['0','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1BjEYKvEcm
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:41:03 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 951 iterations in 0.339s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.62/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.62/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.80  thf(t51_zfmisc_1, conjecture,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.62/0.80       ( r2_hidden @ B @ A ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i,B:$i]:
% 0.62/0.80        ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.62/0.80          ( r2_hidden @ B @ A ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t51_zfmisc_1])).
% 0.62/0.80  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_A)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(d2_tarski, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.62/0.80       ( ![D:$i]:
% 0.62/0.80         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.62/0.80  thf('1', plain,
% 0.62/0.80      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.62/0.80         (((X41) != (X40))
% 0.62/0.80          | (r2_hidden @ X41 @ X42)
% 0.62/0.80          | ((X42) != (k2_tarski @ X43 @ X40)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d2_tarski])).
% 0.62/0.80  thf('2', plain,
% 0.62/0.80      (![X40 : $i, X43 : $i]: (r2_hidden @ X40 @ (k2_tarski @ X43 @ X40))),
% 0.62/0.80      inference('simplify', [status(thm)], ['1'])).
% 0.62/0.80  thf(d5_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.62/0.80       ( ![D:$i]:
% 0.62/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.80           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.62/0.80  thf('3', plain,
% 0.62/0.80      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X2 @ X3)
% 0.62/0.80          | (r2_hidden @ X2 @ X4)
% 0.62/0.80          | (r2_hidden @ X2 @ X5)
% 0.62/0.80          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.80  thf('4', plain,
% 0.62/0.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.80         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.62/0.80          | (r2_hidden @ X2 @ X4)
% 0.62/0.80          | ~ (r2_hidden @ X2 @ X3))),
% 0.62/0.80      inference('simplify', [status(thm)], ['3'])).
% 0.62/0.80  thf('5', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((r2_hidden @ X0 @ X2)
% 0.62/0.80          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ X2)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['2', '4'])).
% 0.62/0.80  thf(t92_xboole_1, axiom,
% 0.62/0.80    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.62/0.80  thf('6', plain, (![X39 : $i]: ((k5_xboole_0 @ X39 @ X39) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf(t3_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.62/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.62/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.62/0.80  thf('7', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i]:
% 0.62/0.80         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 0.62/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.80  thf(t66_xboole_1, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.62/0.80       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.62/0.80  thf('8', plain,
% 0.62/0.80      (![X31 : $i]: ((r1_xboole_0 @ X31 @ X31) | ((X31) != (k1_xboole_0)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.62/0.80  thf('9', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.62/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.62/0.80  thf(t83_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X36 : $i, X37 : $i]:
% 0.62/0.80         (((k4_xboole_0 @ X36 @ X37) = (X36)) | ~ (r1_xboole_0 @ X36 @ X37))),
% 0.62/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.62/0.80  thf('11', plain,
% 0.62/0.80      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('12', plain,
% 0.62/0.80      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X6 @ X5)
% 0.62/0.80          | ~ (r2_hidden @ X6 @ X4)
% 0.62/0.80          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.80  thf('13', plain,
% 0.62/0.80      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X6 @ X4)
% 0.62/0.80          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.62/0.80      inference('simplify', [status(thm)], ['12'])).
% 0.62/0.80  thf('14', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['11', '13'])).
% 0.62/0.80  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.62/0.80      inference('simplify', [status(thm)], ['14'])).
% 0.62/0.80  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.62/0.80      inference('sup-', [status(thm)], ['7', '15'])).
% 0.62/0.80  thf('17', plain,
% 0.62/0.80      (![X36 : $i, X37 : $i]:
% 0.62/0.80         (((k4_xboole_0 @ X36 @ X37) = (X36)) | ~ (r1_xboole_0 @ X36 @ X37))),
% 0.62/0.80      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.62/0.80  thf('18', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.62/0.80  thf('19', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['6', '18'])).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['6', '18'])).
% 0.62/0.80  thf(l36_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 0.62/0.80       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.62/0.80  thf('21', plain,
% 0.62/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 0.62/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 0.62/0.80              (k4_xboole_0 @ X18 @ X20)))),
% 0.62/0.80      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.62/0.80  thf('22', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X1)))
% 0.62/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X2) @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['20', '21'])).
% 0.62/0.80  thf('23', plain, (![X39 : $i]: ((k5_xboole_0 @ X39 @ X39) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf(t2_boole, axiom,
% 0.62/0.80    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.62/0.80  thf('24', plain,
% 0.62/0.80      (![X27 : $i]: ((k3_xboole_0 @ X27 @ k1_xboole_0) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t2_boole])).
% 0.62/0.80  thf('25', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['23', '24'])).
% 0.62/0.80  thf('26', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['16', '17'])).
% 0.62/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.62/0.80  thf('28', plain,
% 0.62/0.80      (![X0 : $i, X2 : $i]:
% 0.62/0.80         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X2)))),
% 0.62/0.80      inference('demod', [status(thm)], ['22', '25', '26', '27'])).
% 0.62/0.80  thf('29', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['19', '28'])).
% 0.62/0.80  thf(d6_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k5_xboole_0 @ A @ B ) =
% 0.62/0.80       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.62/0.80  thf('30', plain,
% 0.62/0.80      (![X8 : $i, X9 : $i]:
% 0.62/0.80         ((k5_xboole_0 @ X8 @ X9)
% 0.62/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ (k4_xboole_0 @ X9 @ X8)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.62/0.80  thf('31', plain,
% 0.62/0.80      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['29', '30'])).
% 0.62/0.80  thf(t81_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.62/0.80       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.62/0.80  thf('32', plain,
% 0.62/0.80      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.62/0.80         ((r1_xboole_0 @ X33 @ (k4_xboole_0 @ X34 @ X35))
% 0.62/0.80          | ~ (r1_xboole_0 @ X34 @ (k4_xboole_0 @ X33 @ X35)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.62/0.80  thf('33', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r1_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.62/0.80          | (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.62/0.80  thf('34', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i]:
% 0.62/0.80         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C @ X11 @ X10) @ X11))),
% 0.62/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.62/0.80  thf('35', plain, (![X39 : $i]: ((k5_xboole_0 @ X39 @ X39) = (k1_xboole_0))),
% 0.62/0.80      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.62/0.80  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.62/0.80      inference('simplify', [status(thm)], ['14'])).
% 0.62/0.80  thf('37', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['35', '36'])).
% 0.62/0.80  thf('38', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['34', '37'])).
% 0.62/0.80  thf('39', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['33', '38'])).
% 0.62/0.80  thf(l24_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.62/0.80  thf('40', plain,
% 0.62/0.80      (![X47 : $i, X48 : $i]:
% 0.62/0.80         (~ (r1_xboole_0 @ (k1_tarski @ X47) @ X48) | ~ (r2_hidden @ X47 @ X48))),
% 0.62/0.80      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.62/0.80  thf('41', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['39', '40'])).
% 0.62/0.80  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['5', '41'])).
% 0.62/0.80  thf('43', plain,
% 0.62/0.80      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.62/0.80         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.62/0.80          | (r2_hidden @ X2 @ X4)
% 0.62/0.80          | ~ (r2_hidden @ X2 @ X3))),
% 0.62/0.80      inference('simplify', [status(thm)], ['3'])).
% 0.62/0.80  thf('44', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((r2_hidden @ X0 @ X1)
% 0.62/0.80          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['42', '43'])).
% 0.62/0.80  thf('45', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['19', '28'])).
% 0.62/0.80  thf('46', plain,
% 0.62/0.80      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 0.62/0.80           = (k2_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ 
% 0.62/0.80              (k4_xboole_0 @ X18 @ X20)))),
% 0.62/0.80      inference('cnf', [status(esa)], [l36_xboole_1])).
% 0.62/0.80  thf('47', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X0))
% 0.62/0.80           = (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['45', '46'])).
% 0.62/0.80  thf('48', plain,
% 0.62/0.80      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(t50_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.62/0.80       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.62/0.80  thf('49', plain,
% 0.62/0.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ X28 @ (k4_xboole_0 @ X29 @ X30))
% 0.62/0.80           = (k4_xboole_0 @ (k3_xboole_0 @ X28 @ X29) @ 
% 0.62/0.80              (k3_xboole_0 @ X28 @ X30)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.62/0.80  thf('50', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.62/0.80           = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['48', '49'])).
% 0.62/0.80  thf(t4_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.62/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.62/0.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.62/0.80  thf('51', plain,
% 0.62/0.80      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X16 @ (k3_xboole_0 @ X14 @ X17))
% 0.62/0.80          | ~ (r1_xboole_0 @ X14 @ X17))),
% 0.62/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.62/0.80  thf('52', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X1 @ 
% 0.62/0.80             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k3_xboole_0 @ sk_A @ X0)))
% 0.62/0.80          | ~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['50', '51'])).
% 0.62/0.80  thf('53', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))
% 0.62/0.80          | ~ (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['47', '52'])).
% 0.62/0.80  thf('54', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.62/0.80      inference('demod', [status(thm)], ['33', '38'])).
% 0.62/0.80  thf('55', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         ~ (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.62/0.80      inference('demod', [status(thm)], ['53', '54'])).
% 0.62/0.80  thf('56', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.62/0.80      inference('sup-', [status(thm)], ['44', '55'])).
% 0.62/0.80  thf('57', plain, ($false), inference('demod', [status(thm)], ['0', '56'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
