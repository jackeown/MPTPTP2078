%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6N4IYB5MLq

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:56 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   21 (  48 expanded)
%              Depth                    :   15
%              Number of atoms          :  515 ( 896 expanded)
%              Number of equality atoms :   29 (  38 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X33: $i] :
      ( ( v1_relat_1 @ X33 )
      | ( r2_hidden @ ( sk_B @ X33 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k3_tarski @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 ) @ X23 )
      | ( r2_hidden @ ( sk_C @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k10_relat_1 @ X39 @ X37 ) )
      | ( r2_hidden @ ( sk_D_3 @ X39 @ X37 @ X38 ) @ X37 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ X0 @ ( sk_C @ ( k10_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k3_tarski @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 ) @ X23 )
      | ( r2_hidden @ ( sk_C @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k10_relat_1 @ X39 @ X37 ) )
      | ( r2_hidden @ ( sk_D_3 @ X39 @ X37 @ X38 ) @ X37 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k3_tarski @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D_3 @ X1 @ X0 @ ( sk_D @ k1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k3_tarski @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X27 @ X23 ) @ X23 )
      | ( r2_hidden @ ( sk_C @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('22',plain,(
    ! [X23: $i,X27: $i] :
      ( ( X27
        = ( k3_tarski @ X23 ) )
      | ( r2_hidden @ ( sk_C @ X27 @ X23 ) @ ( sk_D @ X27 @ X23 ) )
      | ( r2_hidden @ ( sk_C @ X27 @ X23 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('23',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ( r2_hidden @ X24 @ X25 )
      | ( X25
       != ( k3_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X24 @ ( k3_tarski @ X23 ) )
      | ~ ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_tarski @ X0 ) )
      | ( X1
        = ( k3_tarski @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ( X1
        = ( k3_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( X0
        = ( k3_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['13','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('33',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
       != k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k3_tarski @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k10_relat_1 @ X39 @ X37 ) )
      | ( r2_hidden @ ( k4_tarski @ X38 @ ( sk_D_3 @ X39 @ X37 @ X38 ) ) @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) @ ( sk_D_3 @ k1_xboole_0 @ sk_A @ ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) @ ( sk_D_3 @ k1_xboole_0 @ sk_A @ ( sk_C @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 ) ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('42',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6N4IYB5MLq
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:25:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.20/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.20/1.41  % Solved by: fo/fo7.sh
% 1.20/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.20/1.41  % done 496 iterations in 0.957s
% 1.20/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.20/1.41  % SZS output start Refutation
% 1.20/1.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.20/1.41  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.20/1.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.20/1.41  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 1.20/1.41  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 1.20/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.20/1.41  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.20/1.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.20/1.41  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.20/1.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.20/1.41  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.20/1.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.20/1.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.20/1.41  thf(sk_B_type, type, sk_B: $i > $i).
% 1.20/1.41  thf(d1_relat_1, axiom,
% 1.20/1.41    (![A:$i]:
% 1.20/1.41     ( ( v1_relat_1 @ A ) <=>
% 1.20/1.41       ( ![B:$i]:
% 1.20/1.41         ( ~( ( r2_hidden @ B @ A ) & 
% 1.20/1.41              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 1.20/1.41  thf('0', plain,
% 1.20/1.41      (![X33 : $i]: ((v1_relat_1 @ X33) | (r2_hidden @ (sk_B @ X33) @ X33))),
% 1.20/1.41      inference('cnf', [status(esa)], [d1_relat_1])).
% 1.20/1.41  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.20/1.41  thf('1', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.20/1.41  thf(l24_zfmisc_1, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 1.20/1.41  thf('2', plain,
% 1.20/1.41      (![X29 : $i, X30 : $i]:
% 1.20/1.41         (~ (r1_xboole_0 @ (k1_tarski @ X29) @ X30) | ~ (r2_hidden @ X29 @ X30))),
% 1.20/1.41      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 1.20/1.41  thf('3', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('4', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['0', '3'])).
% 1.20/1.41  thf(d4_tarski, axiom,
% 1.20/1.41    (![A:$i,B:$i]:
% 1.20/1.41     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 1.20/1.41       ( ![C:$i]:
% 1.20/1.41         ( ( r2_hidden @ C @ B ) <=>
% 1.20/1.41           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 1.20/1.41  thf('5', plain,
% 1.20/1.41      (![X23 : $i, X27 : $i]:
% 1.20/1.41         (((X27) = (k3_tarski @ X23))
% 1.20/1.41          | (r2_hidden @ (sk_D @ X27 @ X23) @ X23)
% 1.20/1.41          | (r2_hidden @ (sk_C @ X27 @ X23) @ X27))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_tarski])).
% 1.20/1.41  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('7', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 1.20/1.41          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['5', '6'])).
% 1.20/1.41  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 1.20/1.41  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 1.20/1.41      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 1.20/1.41  thf('9', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 1.20/1.41      inference('demod', [status(thm)], ['7', '8'])).
% 1.20/1.41  thf(t166_relat_1, axiom,
% 1.20/1.41    (![A:$i,B:$i,C:$i]:
% 1.20/1.41     ( ( v1_relat_1 @ C ) =>
% 1.20/1.41       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 1.20/1.41         ( ?[D:$i]:
% 1.20/1.41           ( ( r2_hidden @ D @ B ) & 
% 1.20/1.41             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 1.20/1.41             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 1.20/1.41  thf('10', plain,
% 1.20/1.41      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.20/1.41         (~ (r2_hidden @ X38 @ (k10_relat_1 @ X39 @ X37))
% 1.20/1.41          | (r2_hidden @ (sk_D_3 @ X39 @ X37 @ X38) @ X37)
% 1.20/1.41          | ~ (v1_relat_1 @ X39))),
% 1.20/1.41      inference('cnf', [status(esa)], [t166_relat_1])).
% 1.20/1.41  thf('11', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.20/1.41          | ~ (v1_relat_1 @ X1)
% 1.20/1.41          | (r2_hidden @ 
% 1.20/1.41             (sk_D_3 @ X1 @ X0 @ (sk_C @ (k10_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 1.20/1.41             X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['9', '10'])).
% 1.20/1.41  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('13', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['11', '12'])).
% 1.20/1.41  thf('14', plain,
% 1.20/1.41      (![X23 : $i, X27 : $i]:
% 1.20/1.41         (((X27) = (k3_tarski @ X23))
% 1.20/1.41          | (r2_hidden @ (sk_D @ X27 @ X23) @ X23)
% 1.20/1.41          | (r2_hidden @ (sk_C @ X27 @ X23) @ X27))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_tarski])).
% 1.20/1.41  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('16', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X0) @ X0)
% 1.20/1.41          | ((k1_xboole_0) = (k3_tarski @ X0)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['14', '15'])).
% 1.20/1.41  thf('17', plain,
% 1.20/1.41      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.20/1.41         (~ (r2_hidden @ X38 @ (k10_relat_1 @ X39 @ X37))
% 1.20/1.41          | (r2_hidden @ (sk_D_3 @ X39 @ X37 @ X38) @ X37)
% 1.20/1.41          | ~ (v1_relat_1 @ X39))),
% 1.20/1.41      inference('cnf', [status(esa)], [t166_relat_1])).
% 1.20/1.41  thf('18', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ X1 @ X0)))
% 1.20/1.41          | ~ (v1_relat_1 @ X1)
% 1.20/1.41          | (r2_hidden @ 
% 1.20/1.41             (sk_D_3 @ X1 @ X0 @ (sk_D @ k1_xboole_0 @ (k10_relat_1 @ X1 @ X0))) @ 
% 1.20/1.41             X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['16', '17'])).
% 1.20/1.41  thf('19', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('20', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | ((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['18', '19'])).
% 1.20/1.41  thf('21', plain,
% 1.20/1.41      (![X23 : $i, X27 : $i]:
% 1.20/1.41         (((X27) = (k3_tarski @ X23))
% 1.20/1.41          | (r2_hidden @ (sk_D @ X27 @ X23) @ X23)
% 1.20/1.41          | (r2_hidden @ (sk_C @ X27 @ X23) @ X27))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_tarski])).
% 1.20/1.41  thf('22', plain,
% 1.20/1.41      (![X23 : $i, X27 : $i]:
% 1.20/1.41         (((X27) = (k3_tarski @ X23))
% 1.20/1.41          | (r2_hidden @ (sk_C @ X27 @ X23) @ (sk_D @ X27 @ X23))
% 1.20/1.41          | (r2_hidden @ (sk_C @ X27 @ X23) @ X27))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_tarski])).
% 1.20/1.41  thf('23', plain,
% 1.20/1.41      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.20/1.41         (~ (r2_hidden @ X22 @ X23)
% 1.20/1.41          | ~ (r2_hidden @ X24 @ X22)
% 1.20/1.41          | (r2_hidden @ X24 @ X25)
% 1.20/1.41          | ((X25) != (k3_tarski @ X23)))),
% 1.20/1.41      inference('cnf', [status(esa)], [d4_tarski])).
% 1.20/1.41  thf('24', plain,
% 1.20/1.41      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.20/1.41         ((r2_hidden @ X24 @ (k3_tarski @ X23))
% 1.20/1.41          | ~ (r2_hidden @ X24 @ X22)
% 1.20/1.41          | ~ (r2_hidden @ X22 @ X23))),
% 1.20/1.41      inference('simplify', [status(thm)], ['23'])).
% 1.20/1.41  thf('25', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 1.20/1.41          | ((X1) = (k3_tarski @ X0))
% 1.20/1.41          | ~ (r2_hidden @ (sk_D @ X1 @ X0) @ X2)
% 1.20/1.41          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X2)))),
% 1.20/1.41      inference('sup-', [status(thm)], ['22', '24'])).
% 1.20/1.41  thf('26', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 1.20/1.41          | ((X1) = (k3_tarski @ X0))
% 1.20/1.41          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0))
% 1.20/1.41          | ((X1) = (k3_tarski @ X0))
% 1.20/1.41          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.20/1.41      inference('sup-', [status(thm)], ['21', '25'])).
% 1.20/1.41  thf('27', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_tarski @ X0))
% 1.20/1.41          | ((X1) = (k3_tarski @ X0))
% 1.20/1.41          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 1.20/1.41      inference('simplify', [status(thm)], ['26'])).
% 1.20/1.41  thf('28', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.20/1.41           k1_xboole_0)
% 1.20/1.41          | ~ (v1_relat_1 @ X0)
% 1.20/1.41          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)) @ X1)
% 1.20/1.41          | ((X1) = (k3_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0))))),
% 1.20/1.41      inference('sup+', [status(thm)], ['20', '27'])).
% 1.20/1.41  thf('29', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('30', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((X1) = (k3_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0)))
% 1.20/1.41          | (r2_hidden @ (sk_C @ X1 @ (k10_relat_1 @ X0 @ k1_xboole_0)) @ X1)
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['28', '29'])).
% 1.20/1.41  thf('31', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 1.20/1.41          | ~ (v1_relat_1 @ X1)
% 1.20/1.41          | ~ (v1_relat_1 @ X1)
% 1.20/1.41          | ((X0) = (k3_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0))))),
% 1.20/1.41      inference('sup+', [status(thm)], ['13', '30'])).
% 1.20/1.41  thf('32', plain,
% 1.20/1.41      (![X0 : $i, X1 : $i]:
% 1.20/1.41         (((X0) = (k3_tarski @ (k10_relat_1 @ X1 @ k1_xboole_0)))
% 1.20/1.41          | ~ (v1_relat_1 @ X1)
% 1.20/1.41          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 1.20/1.41      inference('simplify', [status(thm)], ['31'])).
% 1.20/1.41  thf(t172_relat_1, conjecture,
% 1.20/1.41    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 1.20/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.20/1.41    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 1.20/1.41    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 1.20/1.41  thf('33', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 1.20/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.20/1.41  thf('34', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (((k3_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0)) != (k1_xboole_0))
% 1.20/1.41          | (r2_hidden @ 
% 1.20/1.41             (sk_C @ (k10_relat_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0) @ 
% 1.20/1.41             (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 1.20/1.41          | ~ (v1_relat_1 @ X0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['32', '33'])).
% 1.20/1.41  thf('35', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | ((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ X0 @ k1_xboole_0))))),
% 1.20/1.41      inference('sup-', [status(thm)], ['18', '19'])).
% 1.20/1.41  thf('36', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | (r2_hidden @ 
% 1.20/1.41             (sk_C @ (k10_relat_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0) @ 
% 1.20/1.41             (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 1.20/1.41      inference('clc', [status(thm)], ['34', '35'])).
% 1.20/1.41  thf('37', plain,
% 1.20/1.41      (![X37 : $i, X38 : $i, X39 : $i]:
% 1.20/1.41         (~ (r2_hidden @ X38 @ (k10_relat_1 @ X39 @ X37))
% 1.20/1.41          | (r2_hidden @ (k4_tarski @ X38 @ (sk_D_3 @ X39 @ X37 @ X38)) @ X39)
% 1.20/1.41          | ~ (v1_relat_1 @ X39))),
% 1.20/1.41      inference('cnf', [status(esa)], [t166_relat_1])).
% 1.20/1.41  thf('38', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.20/1.41          | (r2_hidden @ 
% 1.20/1.41             (k4_tarski @ 
% 1.20/1.41              (sk_C @ (k10_relat_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0) @ 
% 1.20/1.41              (sk_D_3 @ k1_xboole_0 @ sk_A @ 
% 1.20/1.41               (sk_C @ (k10_relat_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))) @ 
% 1.20/1.41             k1_xboole_0))),
% 1.20/1.41      inference('sup-', [status(thm)], ['36', '37'])).
% 1.20/1.41  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['0', '3'])).
% 1.20/1.41  thf('40', plain,
% 1.20/1.41      (![X0 : $i]:
% 1.20/1.41         (~ (v1_relat_1 @ X0)
% 1.20/1.41          | (r2_hidden @ 
% 1.20/1.41             (k4_tarski @ 
% 1.20/1.41              (sk_C @ (k10_relat_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0) @ 
% 1.20/1.41              (sk_D_3 @ k1_xboole_0 @ sk_A @ 
% 1.20/1.41               (sk_C @ (k10_relat_1 @ k1_xboole_0 @ sk_A) @ k1_xboole_0))) @ 
% 1.20/1.41             k1_xboole_0))),
% 1.20/1.41      inference('demod', [status(thm)], ['38', '39'])).
% 1.20/1.41  thf('41', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.20/1.41      inference('sup-', [status(thm)], ['1', '2'])).
% 1.20/1.41  thf('42', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 1.20/1.41      inference('clc', [status(thm)], ['40', '41'])).
% 1.20/1.41  thf('43', plain, ($false), inference('sup-', [status(thm)], ['4', '42'])).
% 1.20/1.41  
% 1.20/1.41  % SZS output end Refutation
% 1.20/1.41  
% 1.20/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
