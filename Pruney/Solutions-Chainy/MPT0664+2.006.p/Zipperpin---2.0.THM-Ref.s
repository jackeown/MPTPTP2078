%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XtF4TG6bbk

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 145 expanded)
%              Number of leaves         :   16 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  611 (1854 expanded)
%              Number of equality atoms :   40 ( 124 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t72_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ B )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ B )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t72_funct_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) )
      | ( X5
        = ( k1_funct_1 @ X4 @ X3 ) )
      | ( X5 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( k1_xboole_0
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_xboole_0
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X4 @ X3 ) )
      | ( r2_hidden @ X3 @ ( k1_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 )
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ( k1_xboole_0
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ( k1_xboole_0
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','30'])).

thf('32',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ ( k1_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 )
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('43',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['39','40','41','42'])).

thf('44',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( k1_xboole_0
    = ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(simplify,[status(thm)],['29'])).

thf('46',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XtF4TG6bbk
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:03:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 29 iterations in 0.025s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.47  thf(t72_funct_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ B ) =>
% 0.22/0.47         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.47        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.47          ( ( r2_hidden @ A @ B ) =>
% 0.22/0.47            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.22/0.47              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t72_funct_1])).
% 0.22/0.47  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(fc8_funct_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.47       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.22/0.47         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X7 : $i, X8 : $i]:
% 0.22/0.47         (~ (v1_funct_1 @ X7)
% 0.22/0.47          | ~ (v1_relat_1 @ X7)
% 0.22/0.47          | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X7 : $i, X8 : $i]:
% 0.22/0.47         (~ (v1_funct_1 @ X7)
% 0.22/0.47          | ~ (v1_relat_1 @ X7)
% 0.22/0.47          | (v1_funct_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.22/0.47      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.22/0.47  thf(d4_funct_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.47       ( ![B:$i,C:$i]:
% 0.22/0.47         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.22/0.47             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.22/0.47               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.47           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.22/0.47             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.22/0.47               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.47         ((r2_hidden @ X3 @ (k1_relat_1 @ X4))
% 0.22/0.47          | ((X5) = (k1_funct_1 @ X4 @ X3))
% 0.22/0.47          | ((X5) != (k1_xboole_0))
% 0.22/0.47          | ~ (v1_funct_1 @ X4)
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X4)
% 0.22/0.47          | ~ (v1_funct_1 @ X4)
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ X4 @ X3))
% 0.22/0.47          | (r2_hidden @ X3 @ (k1_relat_1 @ X4)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.47  thf(t86_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.22/0.47         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 0.22/0.47          | (r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.22/0.47          | ~ (v1_relat_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k1_xboole_0) = (k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.22/0.47          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ X1)
% 0.22/0.47          | (r2_hidden @ X2 @ (k1_relat_1 @ X1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | ~ (v1_funct_1 @ X1)
% 0.22/0.47          | (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.22/0.47          | ~ (v1_relat_1 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k1_xboole_0) = (k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.22/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47          | (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.22/0.47          | ~ (v1_funct_1 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | ~ (v1_funct_1 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ X1)
% 0.22/0.47          | ~ (v1_funct_1 @ X1)
% 0.22/0.47          | (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k1_xboole_0) = (k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2))
% 0.22/0.47          | (r2_hidden @ X2 @ (k1_relat_1 @ X1))
% 0.22/0.47          | ~ (v1_funct_1 @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.47         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_funct_1 @ sk_C @ sk_A))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.47        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_funct_1 @ sk_C @ sk_A))
% 0.22/0.47        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.47  thf('16', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X3 : $i, X4 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X4)
% 0.22/0.47          | ~ (v1_funct_1 @ X4)
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ X4 @ X3))
% 0.22/0.47          | (r2_hidden @ X3 @ (k1_relat_1 @ X4)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['3'])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.22/0.47          | (r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 0.22/0.47          | ~ (v1_relat_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (((k1_xboole_0) = (k1_funct_1 @ X0 @ X1))
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.22/0.47          | ~ (r2_hidden @ X1 @ X2))),
% 0.22/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X1 @ X2)
% 0.22/0.47          | (r2_hidden @ X1 @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X2)))
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ X1)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k1_xboole_0) = (k1_funct_1 @ X0 @ sk_A))
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ X0 @ sk_B))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '20'])).
% 0.22/0.47  thf(t70_funct_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.22/0.47         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X9 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)))
% 0.22/0.47          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X11) @ X9)
% 0.22/0.47              = (k1_funct_1 @ X10 @ X9))
% 0.22/0.47          | ~ (v1_funct_1 @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X10))),
% 0.22/0.47      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.22/0.47  thf('23', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ sk_A))
% 0.22/0.47          | ~ (v1_relat_1 @ X0)
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.22/0.47              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.22/0.47            = (k1_funct_1 @ X0 @ sk_A))
% 0.22/0.47          | ((k1_xboole_0) = (k1_funct_1 @ X0 @ sk_A))
% 0.22/0.47          | ~ (v1_funct_1 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.47         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.47        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.47  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('28', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.22/0.47        | ((k1_xboole_0) = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.47  thf('30', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.47      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.47        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C)))),
% 0.22/0.47      inference('demod', [status(thm)], ['15', '30'])).
% 0.22/0.47  thf('32', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.22/0.47      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.47  thf('33', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.47          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.22/0.47          | (r2_hidden @ X0 @ (k1_relat_1 @ (k7_relat_1 @ X2 @ X1)))
% 0.22/0.47          | ~ (v1_relat_1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.22/0.47  thf('34', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ sk_C)
% 0.22/0.47          | (r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.22/0.47          | ~ (r2_hidden @ sk_A @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.47  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('36', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ X0)))
% 0.22/0.47          | ~ (r2_hidden @ sk_A @ X0))),
% 0.22/0.47      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.47  thf('37', plain,
% 0.22/0.47      ((r2_hidden @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_C @ sk_B)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['0', '36'])).
% 0.22/0.47  thf('38', plain,
% 0.22/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X9 @ (k1_relat_1 @ (k7_relat_1 @ X10 @ X11)))
% 0.22/0.47          | ((k1_funct_1 @ (k7_relat_1 @ X10 @ X11) @ X9)
% 0.22/0.47              = (k1_funct_1 @ X10 @ X9))
% 0.22/0.47          | ~ (v1_funct_1 @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X10))),
% 0.22/0.47      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.22/0.47  thf('39', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_C)
% 0.22/0.47        | ~ (v1_funct_1 @ sk_C)
% 0.22/0.47        | ((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.47            = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.47  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('42', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.47      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.47  thf('43', plain,
% 0.22/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['39', '40', '41', '42'])).
% 0.22/0.47  thf('44', plain,
% 0.22/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.22/0.47         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('45', plain, (((k1_xboole_0) = (k1_funct_1 @ sk_C @ sk_A))),
% 0.22/0.47      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.47  thf('46', plain,
% 0.22/0.47      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.47  thf('47', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
