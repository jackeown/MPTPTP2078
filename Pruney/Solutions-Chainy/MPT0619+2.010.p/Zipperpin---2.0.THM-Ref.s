%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2hTbJsxY5V

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 138 expanded)
%              Number of leaves         :   26 (  51 expanded)
%              Depth                    :   15
%              Number of atoms          :  454 (1241 expanded)
%              Number of equality atoms :   50 ( 144 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 )
      | ( X13
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf(t14_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( k1_relat_1 @ B )
            = ( k1_tarski @ A ) )
         => ( ( k2_relat_1 @ B )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_funct_1])).

thf('1',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('3',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k11_relat_1 @ X15 @ X16 )
        = ( k9_relat_1 @ X15 @ ( k1_tarski @ X16 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('7',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k11_relat_1 @ X19 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ ( k2_tarski @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X21 ) )
      | ( ( k11_relat_1 @ X21 @ X22 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('28',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','28'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( ( sk_C @ X14 @ X13 )
       != X14 )
      | ( X13
        = ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['26','27'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2hTbJsxY5V
% 0.13/0.36  % Computer   : n018.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 10:44:57 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 61 iterations in 0.038s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.52  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.52  thf(t41_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.52          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i]:
% 0.23/0.52         (((X13) = (k1_xboole_0))
% 0.23/0.52          | (r2_hidden @ (sk_C @ X14 @ X13) @ X13)
% 0.23/0.52          | ((X13) = (k1_tarski @ X14)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.23/0.52  thf(t14_funct_1, conjecture,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.52       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.23/0.52         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.23/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.52    (~( ![A:$i,B:$i]:
% 0.23/0.52        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.23/0.52          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.23/0.52            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.23/0.52    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.23/0.52  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t146_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X17 : $i]:
% 0.23/0.52         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 0.23/0.52          | ~ (v1_relat_1 @ X17))),
% 0.23/0.52      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.23/0.52  thf('3', plain,
% 0.23/0.52      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.23/0.52      inference('sup+', [status(thm)], ['1', '2'])).
% 0.23/0.52  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('5', plain,
% 0.23/0.52      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.23/0.52  thf(d16_relat_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ A ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      (![X15 : $i, X16 : $i]:
% 0.23/0.52         (((k11_relat_1 @ X15 @ X16) = (k9_relat_1 @ X15 @ (k1_tarski @ X16)))
% 0.23/0.52          | ~ (v1_relat_1 @ X15))),
% 0.23/0.52      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.23/0.52        | ~ (v1_relat_1 @ sk_B))),
% 0.23/0.52      inference('sup+', [status(thm)], ['5', '6'])).
% 0.23/0.52  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('9', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.52  thf(t204_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ C ) =>
% 0.23/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.52         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.23/0.52  thf('10', plain,
% 0.23/0.52      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X18 @ (k11_relat_1 @ X19 @ X20))
% 0.23/0.52          | (r2_hidden @ (k4_tarski @ X20 @ X18) @ X19)
% 0.23/0.52          | ~ (v1_relat_1 @ X19))),
% 0.23/0.52      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.23/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.23/0.52          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['9', '10'])).
% 0.23/0.52  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.23/0.52          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['11', '12'])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.23/0.52          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.23/0.52          | (r2_hidden @ 
% 0.23/0.52             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.23/0.52      inference('sup-', [status(thm)], ['0', '13'])).
% 0.23/0.52  thf(d10_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.52  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.52  thf(t69_enumset1, axiom,
% 0.23/0.52    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.52  thf('17', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.23/0.52      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.52  thf(t38_zfmisc_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.23/0.52       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.23/0.52         ((r2_hidden @ X9 @ X10) | ~ (r1_tarski @ (k2_tarski @ X9 @ X11) @ X10))),
% 0.23/0.52      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.23/0.52  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['16', '19'])).
% 0.23/0.52  thf('21', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf(t205_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( v1_relat_1 @ B ) =>
% 0.23/0.52       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.23/0.52         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.23/0.52  thf('22', plain,
% 0.23/0.52      (![X21 : $i, X22 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X21))
% 0.23/0.52          | ((k11_relat_1 @ X21 @ X22) != (k1_xboole_0))
% 0.23/0.52          | ~ (v1_relat_1 @ X21))),
% 0.23/0.52      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.23/0.52  thf('23', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.23/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.23/0.52          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.23/0.52  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('25', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.23/0.52          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.23/0.52      inference('demod', [status(thm)], ['23', '24'])).
% 0.23/0.52  thf('26', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['20', '25'])).
% 0.23/0.52  thf('27', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.23/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.23/0.52  thf('28', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('29', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.23/0.52          | (r2_hidden @ 
% 0.23/0.52             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.23/0.52      inference('simplify_reflect-', [status(thm)], ['14', '28'])).
% 0.23/0.52  thf(t8_funct_1, axiom,
% 0.23/0.52    (![A:$i,B:$i,C:$i]:
% 0.23/0.52     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.52       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.23/0.52         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.23/0.52           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.23/0.52  thf('30', plain,
% 0.23/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.23/0.52         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 0.23/0.52          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 0.23/0.52          | ~ (v1_funct_1 @ X24)
% 0.23/0.52          | ~ (v1_relat_1 @ X24))),
% 0.23/0.52      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.23/0.52  thf('31', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.23/0.52          | ~ (v1_relat_1 @ sk_B)
% 0.23/0.52          | ~ (v1_funct_1 @ sk_B)
% 0.23/0.52          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.23/0.52  thf('32', plain, ((v1_relat_1 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('33', plain, ((v1_funct_1 @ sk_B)),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('34', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.23/0.52          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.23/0.52  thf('35', plain,
% 0.23/0.52      (![X13 : $i, X14 : $i]:
% 0.23/0.52         (((X13) = (k1_xboole_0))
% 0.23/0.52          | ((sk_C @ X14 @ X13) != (X14))
% 0.23/0.52          | ((X13) = (k1_tarski @ X14)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.23/0.52  thf('36', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.23/0.52          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.23/0.52          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.23/0.52          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.23/0.52  thf('37', plain,
% 0.23/0.52      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.23/0.52        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.23/0.52      inference('simplify', [status(thm)], ['36'])).
% 0.23/0.52  thf('38', plain,
% 0.23/0.52      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.23/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.52  thf('39', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.23/0.52      inference('demod', [status(thm)], ['26', '27'])).
% 0.23/0.52  thf('40', plain, ($false),
% 0.23/0.52      inference('simplify_reflect-', [status(thm)], ['37', '38', '39'])).
% 0.23/0.52  
% 0.23/0.52  % SZS output end Refutation
% 0.23/0.52  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
