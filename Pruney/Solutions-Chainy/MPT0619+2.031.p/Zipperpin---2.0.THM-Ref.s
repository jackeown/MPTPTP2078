%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r1Y4dCLEJ1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 153 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   23
%              Number of atoms          :  483 (1480 expanded)
%              Number of equality atoms :   60 ( 185 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('0',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k9_relat_1 @ X30 @ ( k1_relat_1 @ X30 ) )
        = ( k2_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('2',plain,
    ( ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k11_relat_1 @ X28 @ X29 )
        = ( k9_relat_1 @ X28 @ ( k1_tarski @ X29 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('6',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X27 @ X26 ) @ X26 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('10',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X31 @ ( k11_relat_1 @ X32 @ X33 ) )
      | ( r2_hidden @ ( k4_tarski @ X33 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X37 @ X39 ) @ X38 )
      | ( X39
        = ( k1_funct_1 @ X38 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( sk_C @ X0 @ ( k2_relat_1 @ sk_B ) )
        = ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( ( sk_C @ X27 @ X26 )
       != X27 )
      | ( X26
        = ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B @ sk_A )
       != X0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_B )
        = ( k1_tarski @ X0 ) )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_B )
      = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k2_relat_1 @ sk_B )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['8','25'])).

thf('27',plain,
    ( ( k2_relat_1 @ sk_B )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X36: $i] :
      ( ( ( k2_relat_1 @ X36 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X36 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('29',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_relat_1 @ sk_B )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('35',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k2_tarski @ X22 @ X24 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('40',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X35 @ ( k1_relat_1 @ X34 ) )
      | ( ( k11_relat_1 @ X34 @ X35 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(simplify,[status(thm)],['44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.r1Y4dCLEJ1
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:33:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 62 iterations in 0.032s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.47  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(t14_funct_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.47         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i]:
% 0.20/0.47        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.47          ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.20/0.47            ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t14_funct_1])).
% 0.20/0.47  thf('0', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t146_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X30 : $i]:
% 0.20/0.47         (((k9_relat_1 @ X30 @ (k1_relat_1 @ X30)) = (k2_relat_1 @ X30))
% 0.20/0.47          | ~ (v1_relat_1 @ X30))),
% 0.20/0.47      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(d16_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X28 : $i, X29 : $i]:
% 0.20/0.47         (((k11_relat_1 @ X28 @ X29) = (k9_relat_1 @ X28 @ (k1_tarski @ X29)))
% 0.20/0.47          | ~ (v1_relat_1 @ X28))),
% 0.20/0.47      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      ((((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.47      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t41_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X26 : $i, X27 : $i]:
% 0.20/0.47         (((X26) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ (sk_C @ X27 @ X26) @ X26)
% 0.20/0.47          | ((X26) = (k1_tarski @ X27)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.47  thf('10', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k2_relat_1 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t204_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.47         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X31 @ (k11_relat_1 @ X32 @ X33))
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ X33 @ X31) @ X32)
% 0.20/0.47          | ~ (v1_relat_1 @ X32))),
% 0.20/0.47      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.47          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.47          | (r2_hidden @ (k4_tarski @ sk_A @ X0) @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | (r2_hidden @ 
% 0.20/0.47             (k4_tarski @ sk_A @ (sk_C @ X0 @ (k2_relat_1 @ sk_B))) @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '14'])).
% 0.20/0.47  thf(t8_funct_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.47         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.47           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.47         (~ (r2_hidden @ (k4_tarski @ X37 @ X39) @ X38)
% 0.20/0.47          | ((X39) = (k1_funct_1 @ X38 @ X37))
% 0.20/0.47          | ~ (v1_funct_1 @ X38)
% 0.20/0.47          | ~ (v1_relat_1 @ X38))),
% 0.20/0.47      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.47          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.47          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.47          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.47  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.47          | ((sk_C @ X0 @ (k2_relat_1 @ sk_B)) = (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X26 : $i, X27 : $i]:
% 0.20/0.47         (((X26) = (k1_xboole_0))
% 0.20/0.47          | ((sk_C @ X27 @ X26) != (X27))
% 0.20/0.47          | ((X26) = (k1_tarski @ X27)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_funct_1 @ sk_B @ sk_A) != (X0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_tarski @ X0))
% 0.20/0.47          | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((k2_relat_1 @ sk_B) = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A))))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (((k2_relat_1 @ sk_B) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf('26', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '25'])).
% 0.20/0.47  thf('27', plain, (((k2_relat_1 @ sk_B) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf(t65_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X36 : $i]:
% 0.20/0.47         (((k2_relat_1 @ X36) != (k1_xboole_0))
% 0.20/0.47          | ((k1_relat_1 @ X36) = (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X36))),
% 0.20/0.47      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.47        | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, (((k1_relat_1 @ sk_B) = (k1_tarski @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      ((((k1_xboole_0) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.20/0.47  thf('33', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.47  thf(t69_enumset1, axiom,
% 0.20/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('34', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.47  thf(t38_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.47       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         ((r2_hidden @ X22 @ X23)
% 0.20/0.47          | ~ (r1_tarski @ (k2_tarski @ X22 @ X24) @ X23))),
% 0.20/0.47      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.47  thf('36', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (r1_tarski @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.47  thf('37', plain,
% 0.20/0.47      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['33', '36'])).
% 0.20/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.47  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.47  thf('39', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.20/0.47      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.47  thf(t205_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ B ) =>
% 0.20/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.47         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i]:
% 0.20/0.47         (~ (r2_hidden @ X35 @ (k1_relat_1 @ X34))
% 0.20/0.47          | ((k11_relat_1 @ X34 @ X35) != (k1_xboole_0))
% 0.20/0.47          | ~ (v1_relat_1 @ X34))),
% 0.20/0.47      inference('cnf', [status(esa)], [t205_relat_1])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ X0) | ((k11_relat_1 @ X0 @ sk_A) != (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '41'])).
% 0.20/0.48  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('44', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ($false), inference('simplify', [status(thm)], ['44'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
