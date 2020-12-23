%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CnjDPOwCsf

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:56 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 204 expanded)
%              Number of leaves         :   22 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  493 (1611 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X38: $i] :
      ( ( X38
        = ( k3_tarski @ X34 ) )
      | ( r2_hidden @ ( sk_D @ X38 @ X34 ) @ X34 )
      | ( r2_hidden @ ( sk_C_1 @ X38 @ X34 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k3_tarski @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t2_zfmisc_1,axiom,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('8',plain,
    ( ( k3_tarski @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t2_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X34: $i,X38: $i] :
      ( ( X38
        = ( k3_tarski @ X34 ) )
      | ( r2_hidden @ ( sk_D @ X38 @ X34 ) @ X34 )
      | ( r2_hidden @ ( sk_C_1 @ X38 @ X34 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X49 @ ( k10_relat_1 @ X50 @ X48 ) )
      | ( r2_hidden @ ( k4_tarski @ X49 @ ( sk_D_3 @ X50 @ X48 @ X49 ) ) @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X2 )
      | ( X2
        = ( k3_tarski @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) @ ( sk_D_3 @ X1 @ X0 @ ( sk_D @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('15',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ( r2_hidden @ ( sk_B @ X44 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('16',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('20',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('24',plain,(
    ! [X34: $i,X38: $i,X39: $i] :
      ( ( X38
        = ( k3_tarski @ X34 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X38 @ X34 ) @ X39 )
      | ~ ( r2_hidden @ X39 @ X34 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X38 @ X34 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ( X0
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_tarski @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k10_relat_1 @ k1_xboole_0 @ X1 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_1 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ k1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( r2_hidden @ X49 @ ( k10_relat_1 @ X50 @ X48 ) )
      | ( r2_hidden @ ( k4_tarski @ X49 @ ( sk_D_3 @ X50 @ X48 @ X49 ) ) @ X50 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ ( sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ k1_xboole_0 @ ( sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CnjDPOwCsf
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 477 iterations in 0.665s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.91/1.10  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.10  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.91/1.10  thf(sk_D_3_type, type, sk_D_3: $i > $i > $i > $i).
% 0.91/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.10  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.91/1.10  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(t172_relat_1, conjecture,
% 0.91/1.10    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.91/1.10  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(d4_tarski, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.91/1.10       ( ![C:$i]:
% 0.91/1.10         ( ( r2_hidden @ C @ B ) <=>
% 0.91/1.10           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X34 : $i, X38 : $i]:
% 0.91/1.10         (((X38) = (k3_tarski @ X34))
% 0.91/1.10          | (r2_hidden @ (sk_D @ X38 @ X34) @ X34)
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X38 @ X34) @ X38))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.91/1.10  thf(t2_boole, axiom,
% 0.91/1.10    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_boole])).
% 0.91/1.10  thf(t4_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.10            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.91/1.10       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.91/1.10            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.91/1.10          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.10  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.91/1.10  thf('5', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.91/1.10      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.91/1.10  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.10      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.91/1.10          | ((X0) = (k3_tarski @ k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['1', '6'])).
% 0.91/1.10  thf(t2_zfmisc_1, axiom, (( k3_tarski @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.91/1.10  thf('8', plain, (((k3_tarski @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_zfmisc_1])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.91/1.10          | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X34 : $i, X38 : $i]:
% 0.91/1.10         (((X38) = (k3_tarski @ X34))
% 0.91/1.10          | (r2_hidden @ (sk_D @ X38 @ X34) @ X34)
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X38 @ X34) @ X38))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.91/1.10  thf(t166_relat_1, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( v1_relat_1 @ C ) =>
% 0.91/1.10       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.91/1.10         ( ?[D:$i]:
% 0.91/1.10           ( ( r2_hidden @ D @ B ) & 
% 0.91/1.10             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.91/1.10             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.91/1.10  thf('11', plain,
% 0.91/1.10      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X49 @ (k10_relat_1 @ X50 @ X48))
% 0.91/1.10          | (r2_hidden @ (k4_tarski @ X49 @ (sk_D_3 @ X50 @ X48 @ X49)) @ X50)
% 0.91/1.10          | ~ (v1_relat_1 @ X50))),
% 0.91/1.10      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         ((r2_hidden @ (sk_C_1 @ X2 @ (k10_relat_1 @ X1 @ X0)) @ X2)
% 0.91/1.10          | ((X2) = (k3_tarski @ (k10_relat_1 @ X1 @ X0)))
% 0.91/1.10          | ~ (v1_relat_1 @ X1)
% 0.91/1.10          | (r2_hidden @ 
% 0.91/1.10             (k4_tarski @ (sk_D @ X2 @ (k10_relat_1 @ X1 @ X0)) @ 
% 0.91/1.10              (sk_D_3 @ X1 @ X0 @ (sk_D @ X2 @ (k10_relat_1 @ X1 @ X0)))) @ 
% 0.91/1.10             X1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.10  thf('13', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.10      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (v1_relat_1 @ k1_xboole_0)
% 0.91/1.10          | ((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.10  thf(d1_relat_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( v1_relat_1 @ A ) <=>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ~( ( r2_hidden @ B @ A ) & 
% 0.91/1.10              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (![X44 : $i]: ((v1_relat_1 @ X44) | (r2_hidden @ (sk_B @ X44) @ X44))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.91/1.10  thf('16', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.10      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.10  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.91/1.10      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.91/1.10      inference('demod', [status(thm)], ['14', '17'])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.91/1.10      inference('demod', [status(thm)], ['14', '17'])).
% 0.91/1.10  thf('20', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.10      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X1) = (k1_xboole_0))
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.91/1.10      inference('demod', [status(thm)], ['18', '21'])).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X1) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))
% 0.91/1.10          | (r2_hidden @ (sk_C_1 @ X1 @ (k10_relat_1 @ k1_xboole_0 @ X0)) @ X1))),
% 0.91/1.10      inference('demod', [status(thm)], ['14', '17'])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X34 : $i, X38 : $i, X39 : $i]:
% 0.91/1.10         (((X38) = (k3_tarski @ X34))
% 0.91/1.10          | ~ (r2_hidden @ (sk_C_1 @ X38 @ X34) @ X39)
% 0.91/1.10          | ~ (r2_hidden @ X39 @ X34)
% 0.91/1.10          | ~ (r2_hidden @ (sk_C_1 @ X38 @ X34) @ X38))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_tarski])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X1)))
% 0.91/1.10          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)) @ 
% 0.91/1.10               X0)
% 0.91/1.10          | ~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.91/1.10          | ((X0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X1))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.10  thf('26', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.91/1.10          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)) @ 
% 0.91/1.10               X0)
% 0.91/1.10          | ((X0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X1))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['25'])).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k1_xboole_0) = (k3_tarski @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.91/1.10          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)) @ 
% 0.91/1.10               X0)
% 0.91/1.10          | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('demod', [status(thm)], ['26', '27'])).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X0) = (k1_xboole_0))
% 0.91/1.10          | ((X0) = (k1_xboole_0))
% 0.91/1.10          | ~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['22', '28'])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X0 @ (k10_relat_1 @ k1_xboole_0 @ X1))
% 0.91/1.10          | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['29'])).
% 0.91/1.10  thf('31', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.91/1.10          | ((sk_C_1 @ (k10_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.91/1.10              = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '30'])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.91/1.10          | ((X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('demod', [status(thm)], ['7', '8'])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r2_hidden @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.91/1.10          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.91/1.10          | ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['31', '32'])).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.91/1.10          | (r2_hidden @ k1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['33'])).
% 0.91/1.10  thf('35', plain,
% 0.91/1.10      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X49 @ (k10_relat_1 @ X50 @ X48))
% 0.91/1.10          | (r2_hidden @ (k4_tarski @ X49 @ (sk_D_3 @ X50 @ X48 @ X49)) @ X50)
% 0.91/1.10          | ~ (v1_relat_1 @ X50))),
% 0.91/1.10      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.91/1.10  thf('36', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.91/1.10          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.91/1.10          | (r2_hidden @ 
% 0.91/1.10             (k4_tarski @ k1_xboole_0 @ 
% 0.91/1.10              (sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.91/1.10             k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.10  thf('37', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.91/1.10      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.10  thf('38', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.91/1.10          | (r2_hidden @ 
% 0.91/1.10             (k4_tarski @ k1_xboole_0 @ 
% 0.91/1.10              (sk_D_3 @ k1_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 0.91/1.10             k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['36', '37'])).
% 0.91/1.10  thf('39', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.91/1.10      inference('demod', [status(thm)], ['4', '5'])).
% 0.91/1.10  thf('40', plain,
% 0.91/1.10      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.10      inference('clc', [status(thm)], ['38', '39'])).
% 0.91/1.10  thf('41', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['0', '40'])).
% 0.91/1.10  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
