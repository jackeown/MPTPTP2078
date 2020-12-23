%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.88LnwPIxxQ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 142 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  459 (1263 expanded)
%              Number of equality atoms :   49 ( 144 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X35 @ X34 ) @ X34 )
      | ( X34
        = ( k1_tarski @ X35 ) ) ) ),
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
    ! [X38: $i] :
      ( ( ( k9_relat_1 @ X38 @ ( k1_relat_1 @ X38 ) )
        = ( k2_relat_1 @ X38 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k11_relat_1 @ X36 @ X37 )
        = ( k9_relat_1 @ X36 @ ( k1_tarski @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
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
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k11_relat_1 @ X40 @ X41 ) )
      | ( r2_hidden @ ( k4_tarski @ X41 @ X39 ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X31 )
      | ~ ( r1_tarski @ ( k2_tarski @ X30 @ X32 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ X42 ) )
      | ( ( k11_relat_1 @ X42 @ X43 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( ( k11_relat_1 @ sk_B @ X0 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('29',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','29'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X44 @ X46 ) @ X45 )
      | ( X46
        = ( k1_funct_1 @ X45 @ X44 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ! [X34: $i,X35: $i] :
      ( ( X34 = k1_xboole_0 )
      | ( ( sk_C @ X35 @ X34 )
       != X35 )
      | ( X34
        = ( k1_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ( k2_relat_1 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['38','39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.88LnwPIxxQ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 63 iterations in 0.038s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(t41_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.49          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         (((X34) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ (sk_C @ X35 @ X34) @ X34)
% 0.20/0.49          | ((X34) = (k1_tarski @ X35)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.49  thf(t14_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.49         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.49          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.49            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.20/0.49  thf('1', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t146_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X38 : $i]:
% 0.20/0.49         (((k9_relat_1 @ X38 @ (k1_relat_1 @ X38)) = (k2_relat_1 @ X38))
% 0.20/0.49          | ~ (v1_relat_1 @ X38))),
% 0.20/0.49      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf(d16_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X36 : $i, X37 : $i]:
% 0.20/0.49         (((k11_relat_1 @ X36 @ X37) = (k9_relat_1 @ X36 @ (k1_tarski @ X37)))
% 0.20/0.49          | ~ (v1_relat_1 @ X36))),
% 0.20/0.49      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.20/0.49        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf(t204_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X39 @ (k11_relat_1 @ X40 @ X41))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ X41 @ X39) @ X40)
% 0.20/0.49          | ~ (v1_relat_1 @ X40))),
% 0.20/0.49      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.49  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.49          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.49          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '13'])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('15', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t12_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i]:
% 0.20/0.49         (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X28 @ X29))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.20/0.49  thf('17', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf(t38_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.49         ((r2_hidden @ X30 @ X31)
% 0.20/0.49          | ~ (r1_tarski @ (k2_tarski @ X30 @ X32) @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '19'])).
% 0.20/0.49  thf('21', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['15', '20'])).
% 0.20/0.49  thf('22', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t205_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.49         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X42 : $i, X43 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X43 @ (k1_relat_1 @ X42))
% 0.20/0.49          | ((k11_relat_1 @ X42 @ X43) != (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X42))),
% 0.20/0.49      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.49          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.20/0.49          | ((k11_relat_1 @ sk_B @ X0) != (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '26'])).
% 0.20/0.49  thf('28', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('29', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['14', '29'])).
% 0.20/0.49  thf(t8_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.49         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.49           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X44 @ X46) @ X45)
% 0.20/0.49          | ((X46) = (k1_funct_1 @ X45 @ X44))
% 0.20/0.49          | ~ (v1_funct_1 @ X45)
% 0.20/0.49          | ~ (v1_relat_1 @ X45))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.49          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.49          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.49  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('34', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.49          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         (((X34) = (k1_xboole_0))
% 0.20/0.49          | ((sk_C @ X35 @ X34) != (X35))
% 0.20/0.49          | ((X34) = (k1_tarski @ X35)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.20/0.49          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.49          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.49          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.49        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.49      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('40', plain, (((k2_relat_1 @ sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('41', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['38', '39', '40'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
