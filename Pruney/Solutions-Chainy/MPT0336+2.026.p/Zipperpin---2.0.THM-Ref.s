%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QsSjKkK3Zt

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:23 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 110 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   16
%              Number of atoms          :  498 ( 887 expanded)
%              Number of equality atoms :   22 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
      | ( r2_hidden @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k3_xboole_0 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k3_xboole_0 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','23'])).

thf('25',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('34',plain,(
    ! [X25: $i] :
      ( r1_xboole_0 @ X25 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','33','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['37','42'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
      | ~ ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QsSjKkK3Zt
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 12:37:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 1.14/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.35  % Solved by: fo/fo7.sh
% 1.14/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.35  % done 1351 iterations in 0.880s
% 1.14/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.35  % SZS output start Refutation
% 1.14/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.35  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.14/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.14/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.14/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.14/1.35  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.14/1.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.14/1.35  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.14/1.35  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.35  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.14/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.35  thf(t149_zfmisc_1, conjecture,
% 1.14/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.35     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.14/1.35         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.14/1.35       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.14/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.35    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.35        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.14/1.35            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.14/1.35          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.14/1.35    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.14/1.35  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.14/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.35  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.14/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.35  thf(symmetry_r1_xboole_0, axiom,
% 1.14/1.35    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.14/1.35  thf('2', plain,
% 1.14/1.35      (![X11 : $i, X12 : $i]:
% 1.14/1.35         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 1.14/1.35      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.14/1.35  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.14/1.35      inference('sup-', [status(thm)], ['1', '2'])).
% 1.14/1.35  thf(t4_xboole_0, axiom,
% 1.14/1.35    (![A:$i,B:$i]:
% 1.14/1.35     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.14/1.35            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.14/1.35       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.14/1.35            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.14/1.35  thf('4', plain,
% 1.14/1.35      (![X13 : $i, X14 : $i]:
% 1.14/1.35         ((r1_xboole_0 @ X13 @ X14)
% 1.14/1.35          | (r2_hidden @ (sk_C @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 1.14/1.35      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.14/1.35  thf(l27_zfmisc_1, axiom,
% 1.14/1.35    (![A:$i,B:$i]:
% 1.14/1.35     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.14/1.35  thf('5', plain,
% 1.14/1.35      (![X36 : $i, X37 : $i]:
% 1.14/1.35         ((r1_xboole_0 @ (k1_tarski @ X36) @ X37) | (r2_hidden @ X36 @ X37))),
% 1.14/1.35      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.14/1.35  thf('6', plain,
% 1.14/1.35      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 1.14/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.35  thf(commutativity_k3_xboole_0, axiom,
% 1.14/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.14/1.35  thf('7', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.35  thf('8', plain,
% 1.14/1.35      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.14/1.35      inference('demod', [status(thm)], ['6', '7'])).
% 1.14/1.35  thf(t28_xboole_1, axiom,
% 1.14/1.35    (![A:$i,B:$i]:
% 1.14/1.35     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.14/1.35  thf('9', plain,
% 1.14/1.35      (![X23 : $i, X24 : $i]:
% 1.14/1.35         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 1.14/1.35      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.14/1.35  thf('10', plain,
% 1.14/1.35      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 1.14/1.35         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.14/1.35      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.35  thf('11', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.35  thf(t16_xboole_1, axiom,
% 1.14/1.35    (![A:$i,B:$i,C:$i]:
% 1.14/1.35     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.14/1.35       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.14/1.35  thf('12', plain,
% 1.14/1.35      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.14/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22)
% 1.14/1.35           = (k3_xboole_0 @ X20 @ (k3_xboole_0 @ X21 @ X22)))),
% 1.14/1.35      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.14/1.35  thf('13', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.14/1.35           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.14/1.35      inference('sup+', [status(thm)], ['11', '12'])).
% 1.14/1.35  thf('14', plain,
% 1.14/1.35      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))
% 1.14/1.35         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.14/1.35      inference('demod', [status(thm)], ['10', '13'])).
% 1.14/1.35  thf('15', plain,
% 1.14/1.35      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.14/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X20 @ X21) @ X22)
% 1.14/1.35           = (k3_xboole_0 @ X20 @ (k3_xboole_0 @ X21 @ X22)))),
% 1.14/1.35      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.14/1.35  thf('16', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.35  thf('17', plain,
% 1.14/1.35      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 1.14/1.35          | ~ (r1_xboole_0 @ X13 @ X16))),
% 1.14/1.35      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.14/1.35  thf('18', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.14/1.35          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.14/1.35      inference('sup-', [status(thm)], ['16', '17'])).
% 1.14/1.35  thf('19', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.14/1.35          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['15', '18'])).
% 1.14/1.35  thf('20', plain,
% 1.14/1.35      (![X0 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.14/1.35          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['14', '19'])).
% 1.14/1.35  thf('21', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.14/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.14/1.35  thf('22', plain,
% 1.14/1.35      (![X0 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.14/1.35          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.14/1.35      inference('demod', [status(thm)], ['20', '21'])).
% 1.14/1.35  thf('23', plain,
% 1.14/1.35      (![X0 : $i]:
% 1.14/1.35         ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.14/1.35          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['5', '22'])).
% 1.14/1.35  thf('24', plain,
% 1.14/1.35      (((r1_xboole_0 @ sk_B @ sk_A)
% 1.14/1.35        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['4', '23'])).
% 1.14/1.35  thf('25', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 1.14/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.35  thf(d4_xboole_0, axiom,
% 1.14/1.35    (![A:$i,B:$i,C:$i]:
% 1.14/1.35     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.14/1.35       ( ![D:$i]:
% 1.14/1.35         ( ( r2_hidden @ D @ C ) <=>
% 1.14/1.35           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.14/1.35  thf('26', plain,
% 1.14/1.35      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X2 @ X3)
% 1.14/1.35          | ~ (r2_hidden @ X2 @ X4)
% 1.14/1.35          | (r2_hidden @ X2 @ X5)
% 1.14/1.35          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.14/1.35      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.14/1.35  thf('27', plain,
% 1.14/1.35      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.14/1.35         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.14/1.35          | ~ (r2_hidden @ X2 @ X4)
% 1.14/1.35          | ~ (r2_hidden @ X2 @ X3))),
% 1.14/1.35      inference('simplify', [status(thm)], ['26'])).
% 1.14/1.35  thf('28', plain,
% 1.14/1.35      (![X0 : $i]:
% 1.14/1.35         (~ (r2_hidden @ sk_D_1 @ X0)
% 1.14/1.35          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['25', '27'])).
% 1.14/1.35  thf('29', plain,
% 1.14/1.35      (((r1_xboole_0 @ sk_B @ sk_A)
% 1.14/1.35        | (r2_hidden @ sk_D_1 @ 
% 1.14/1.35           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['24', '28'])).
% 1.14/1.35  thf('30', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.14/1.35           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.14/1.35      inference('sup+', [status(thm)], ['11', '12'])).
% 1.14/1.35  thf('31', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.14/1.35      inference('sup-', [status(thm)], ['1', '2'])).
% 1.14/1.35  thf(d7_xboole_0, axiom,
% 1.14/1.35    (![A:$i,B:$i]:
% 1.14/1.35     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.14/1.35       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.14/1.35  thf('32', plain,
% 1.14/1.35      (![X8 : $i, X9 : $i]:
% 1.14/1.35         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 1.14/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.14/1.35  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.14/1.35      inference('sup-', [status(thm)], ['31', '32'])).
% 1.14/1.35  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.14/1.35  thf('34', plain, (![X25 : $i]: (r1_xboole_0 @ X25 @ k1_xboole_0)),
% 1.14/1.35      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.14/1.35  thf('35', plain,
% 1.14/1.35      (![X8 : $i, X9 : $i]:
% 1.14/1.35         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 1.14/1.35      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.14/1.35  thf('36', plain,
% 1.14/1.35      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.14/1.35      inference('sup-', [status(thm)], ['34', '35'])).
% 1.14/1.35  thf('37', plain,
% 1.14/1.35      (((r1_xboole_0 @ sk_B @ sk_A) | (r2_hidden @ sk_D_1 @ k1_xboole_0))),
% 1.14/1.35      inference('demod', [status(thm)], ['29', '30', '33', '36'])).
% 1.14/1.35  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.14/1.35      inference('sup-', [status(thm)], ['31', '32'])).
% 1.14/1.35  thf('39', plain,
% 1.14/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.14/1.35          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.14/1.35      inference('sup-', [status(thm)], ['16', '17'])).
% 1.14/1.35  thf('40', plain,
% 1.14/1.35      (![X0 : $i]:
% 1.14/1.35         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_C_1 @ sk_B))),
% 1.14/1.35      inference('sup-', [status(thm)], ['38', '39'])).
% 1.14/1.35  thf('41', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.14/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.35  thf('42', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.14/1.35      inference('demod', [status(thm)], ['40', '41'])).
% 1.14/1.35  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.14/1.35      inference('clc', [status(thm)], ['37', '42'])).
% 1.14/1.35  thf(t70_xboole_1, axiom,
% 1.14/1.35    (![A:$i,B:$i,C:$i]:
% 1.14/1.35     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.14/1.35            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.14/1.35       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.14/1.35            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.14/1.35  thf('44', plain,
% 1.14/1.35      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.14/1.35         ((r1_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 1.14/1.35          | ~ (r1_xboole_0 @ X26 @ X27)
% 1.14/1.35          | ~ (r1_xboole_0 @ X26 @ X28))),
% 1.14/1.35      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.14/1.35  thf('45', plain,
% 1.14/1.35      (![X0 : $i]:
% 1.14/1.35         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.14/1.35          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.14/1.35      inference('sup-', [status(thm)], ['43', '44'])).
% 1.14/1.35  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.14/1.35      inference('sup-', [status(thm)], ['3', '45'])).
% 1.14/1.35  thf('47', plain,
% 1.14/1.35      (![X11 : $i, X12 : $i]:
% 1.14/1.35         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 1.14/1.35      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.14/1.35  thf('48', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.14/1.35      inference('sup-', [status(thm)], ['46', '47'])).
% 1.14/1.35  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 1.14/1.35  
% 1.14/1.35  % SZS output end Refutation
% 1.14/1.35  
% 1.18/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
