%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x5o6waxDvA

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:24 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 127 expanded)
%              Number of leaves         :   22 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  437 ( 761 expanded)
%              Number of equality atoms :   49 (  83 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X12: $i] :
      ( ( X12
        = ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X9 ) @ ( sk_C @ X12 @ X9 ) ) @ X9 )
      | ( r2_hidden @ ( sk_C @ X12 @ X9 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i] :
      ( ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('27',plain,(
    ! [X18: $i] :
      ( ( ( k2_relat_1 @ X18 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('30',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k1_relat_1 @ X1 )
         != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','32'])).

thf('34',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X1 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','35'])).

thf('37',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('48',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['25','51'])).

thf('53',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.x5o6waxDvA
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:51:18 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 198 iterations in 0.125s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.41/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.60  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf(d5_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]:
% 0.41/0.60         ( ( r2_hidden @ C @ B ) <=>
% 0.41/0.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.41/0.60  thf('2', plain,
% 0.41/0.60      (![X9 : $i, X12 : $i]:
% 0.41/0.60         (((X12) = (k2_relat_1 @ X9))
% 0.41/0.60          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X9) @ (sk_C @ X12 @ X9)) @ 
% 0.41/0.60             X9)
% 0.41/0.60          | (r2_hidden @ (sk_C @ X12 @ X9) @ X12))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('3', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.41/0.60          | ((X1) = (k2_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1)
% 0.41/0.60          | ((X0) = (k2_relat_1 @ X1))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X0 : $i]: (((k1_xboole_0) = (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '6'])).
% 0.41/0.60  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['7', '8'])).
% 0.41/0.60  thf(dt_k4_relat_1, axiom,
% 0.41/0.60    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (![X14 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X14)) | ~ (v1_relat_1 @ X14))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.41/0.60  thf(t37_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_relat_1 @ A ) =>
% 0.41/0.60       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.41/0.60         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_relat_1 @ X18) = (k1_relat_1 @ (k4_relat_1 @ X18)))
% 0.41/0.60          | ~ (v1_relat_1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.41/0.60  thf(fc8_relat_1, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.41/0.60       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X17 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (k1_relat_1 @ X17))
% 0.41/0.60          | ~ (v1_relat_1 @ X17)
% 0.41/0.60          | (v1_xboole_0 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_relat_1 @ X0)
% 0.41/0.60          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '13'])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.41/0.60          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_relat_1 @ X0)
% 0.41/0.60          | (v1_xboole_0 @ (k4_relat_1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['9', '15'])).
% 0.41/0.60  thf(t7_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.41/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('19', plain,
% 0.41/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf(t113_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X5 : $i, X6 : $i]:
% 0.41/0.60         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.41/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.60  thf(fc6_relat_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.60  thf('22', plain,
% 0.41/0.60      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.41/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.60  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.41/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.41/0.60  thf('24', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['19', '23'])).
% 0.41/0.60  thf('25', plain,
% 0.41/0.60      (![X0 : $i]: ((v1_xboole_0 @ (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('clc', [status(thm)], ['16', '24'])).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X0 : $i]: (((k1_xboole_0) = (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['1', '6'])).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X18 : $i]:
% 0.41/0.60         (((k2_relat_1 @ X18) = (k1_relat_1 @ (k4_relat_1 @ X18)))
% 0.41/0.60          | ~ (v1_relat_1 @ X18))),
% 0.41/0.60      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.60  thf(t60_relat_1, conjecture,
% 0.41/0.60    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.41/0.60     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.41/0.60        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.41/0.60        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('split', [status(esa)], ['30'])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['29', '31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      ((![X0 : $i, X1 : $i]:
% 0.41/0.60          (((k1_relat_1 @ X1) != (X0))
% 0.41/0.60           | ~ (v1_xboole_0 @ X0)
% 0.41/0.60           | ~ (v1_xboole_0 @ X1)))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['28', '32'])).
% 0.41/0.60  thf('34', plain,
% 0.41/0.60      ((![X1 : $i]:
% 0.41/0.60          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k1_relat_1 @ X1))))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.41/0.60           | ~ (v1_relat_1 @ X0)
% 0.41/0.60           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['27', '34'])).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.41/0.60           | ~ (v1_xboole_0 @ X0)
% 0.41/0.60           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.41/0.60           | ~ (v1_relat_1 @ X0)))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '35'])).
% 0.41/0.60  thf('37', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          (~ (v1_xboole_0 @ X0)
% 0.41/0.60           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.41/0.60           | ~ (v1_relat_1 @ X0)))
% 0.41/0.60         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X1)
% 0.41/0.60          | ((X0) = (k2_relat_1 @ X1))
% 0.41/0.60          | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['4', '5'])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.41/0.60         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('split', [status(esa)], ['30'])).
% 0.41/0.60  thf('41', plain,
% 0.41/0.60      ((![X0 : $i]:
% 0.41/0.60          (((X0) != (k1_xboole_0))
% 0.41/0.60           | ~ (v1_xboole_0 @ X0)
% 0.41/0.60           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.41/0.60         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.60  thf('42', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      ((![X0 : $i]: (((X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.41/0.60         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('demod', [status(thm)], ['41', '42'])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.41/0.60         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.41/0.60      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.60  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.60  thf('46', plain, ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.41/0.60      inference('simplify_reflect+', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.41/0.60       ~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.41/0.60      inference('split', [status(esa)], ['30'])).
% 0.41/0.60  thf('48', plain, (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.41/0.60      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X0)
% 0.41/0.60          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.41/0.60          | ~ (v1_relat_1 @ X0))),
% 0.41/0.60      inference('simpl_trail', [status(thm)], ['38', '48'])).
% 0.41/0.60  thf('50', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['19', '23'])).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X0 : $i]: (~ (v1_xboole_0 @ (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('clc', [status(thm)], ['49', '50'])).
% 0.41/0.60  thf('52', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.41/0.60      inference('clc', [status(thm)], ['25', '51'])).
% 0.41/0.60  thf('53', plain, ($false), inference('sup-', [status(thm)], ['0', '52'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
