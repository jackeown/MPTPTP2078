%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iKYpUTkRBD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:50 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 151 expanded)
%              Number of leaves         :   19 (  48 expanded)
%              Depth                    :   16
%              Number of atoms          :  605 (1911 expanded)
%              Number of equality atoms :   43 ( 138 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(fc8_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_funct_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_funct_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ( X12
       != ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('4',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( ( k1_funct_1 @ X11 @ X10 )
        = k1_xboole_0 )
      | ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X8 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t70_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) ) )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X17 @ X18 ) @ X16 )
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ( ( k1_funct_1 @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k1_funct_1 @ sk_C @ sk_A )
     != ( k1_funct_1 @ sk_C @ sk_A ) )
    | ( ( k1_funct_1 @ sk_C @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['10','28'])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C ) @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
      = ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_funct_1 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['27'])).

thf('40',plain,
    ( ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['10','28'])).

thf('42',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iKYpUTkRBD
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:05:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.56  % Solved by: fo/fo7.sh
% 0.19/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.56  % done 152 iterations in 0.108s
% 0.19/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.56  % SZS output start Refutation
% 0.19/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.56  thf(dt_k7_relat_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.19/0.56  thf('0', plain,
% 0.19/0.56      (![X6 : $i, X7 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X6) | (v1_relat_1 @ (k7_relat_1 @ X6 @ X7)))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.19/0.56  thf(fc8_funct_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.56       ( ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.19/0.56         ( v1_funct_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.19/0.56  thf('1', plain,
% 0.19/0.56      (![X14 : $i, X15 : $i]:
% 0.19/0.56         (~ (v1_funct_1 @ X14)
% 0.19/0.56          | ~ (v1_relat_1 @ X14)
% 0.19/0.56          | (v1_funct_1 @ (k7_relat_1 @ X14 @ X15)))),
% 0.19/0.56      inference('cnf', [status(esa)], [fc8_funct_1])).
% 0.19/0.56  thf(t90_relat_1, axiom,
% 0.19/0.56    (![A:$i,B:$i]:
% 0.19/0.56     ( ( v1_relat_1 @ B ) =>
% 0.19/0.56       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.19/0.56         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.56  thf('2', plain,
% 0.19/0.56      (![X8 : $i, X9 : $i]:
% 0.19/0.56         (((k1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 0.19/0.56            = (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.19/0.56          | ~ (v1_relat_1 @ X8))),
% 0.19/0.56      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.19/0.56  thf(d4_funct_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.19/0.56       ( ![B:$i,C:$i]:
% 0.19/0.56         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.19/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.19/0.56               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.56           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.19/0.56             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.19/0.56               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.19/0.56  thf('3', plain,
% 0.19/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.56         ((r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.19/0.56          | ((X12) = (k1_xboole_0))
% 0.19/0.56          | ((X12) != (k1_funct_1 @ X11 @ X10))
% 0.19/0.56          | ~ (v1_funct_1 @ X11)
% 0.19/0.56          | ~ (v1_relat_1 @ X11))),
% 0.19/0.56      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.19/0.56  thf('4', plain,
% 0.19/0.56      (![X10 : $i, X11 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X11)
% 0.19/0.56          | ~ (v1_funct_1 @ X11)
% 0.19/0.56          | ((k1_funct_1 @ X11 @ X10) = (k1_xboole_0))
% 0.19/0.56          | (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.56  thf('5', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.19/0.56      inference('sup+', [status(thm)], ['2', '4'])).
% 0.19/0.56  thf('6', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['1', '5'])).
% 0.19/0.56  thf('7', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1))),
% 0.19/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.56  thf('8', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.19/0.56          | (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.56  thf('9', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1))),
% 0.19/0.56      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.56  thf(t72_funct_1, conjecture,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.56       ( ( r2_hidden @ A @ B ) =>
% 0.19/0.56         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.19/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.56        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.56          ( ( r2_hidden @ A @ B ) =>
% 0.19/0.56            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.19/0.56              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.19/0.56    inference('cnf.neg', [status(esa)], [t72_funct_1])).
% 0.19/0.56  thf('10', plain,
% 0.19/0.56      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.56         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('11', plain,
% 0.19/0.56      (![X10 : $i, X11 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X11)
% 0.19/0.56          | ~ (v1_funct_1 @ X11)
% 0.19/0.56          | ((k1_funct_1 @ X11 @ X10) = (k1_xboole_0))
% 0.19/0.56          | (r2_hidden @ X10 @ (k1_relat_1 @ X11)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['3'])).
% 0.19/0.56  thf('12', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(d4_xboole_0, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.56       ( ![D:$i]:
% 0.19/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.56  thf('13', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.56          | ~ (r2_hidden @ X0 @ X2)
% 0.19/0.56          | (r2_hidden @ X0 @ X3)
% 0.19/0.56          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.56  thf('14', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         ((r2_hidden @ X0 @ (k3_xboole_0 @ X1 @ X2))
% 0.19/0.56          | ~ (r2_hidden @ X0 @ X2)
% 0.19/0.56          | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.56      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.56  thf('15', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (r2_hidden @ sk_A @ X0)
% 0.19/0.56          | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.56  thf('16', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ~ (v1_relat_1 @ X0)
% 0.19/0.56          | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ X0) @ sk_B)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['11', '15'])).
% 0.19/0.56  thf('17', plain,
% 0.19/0.56      (![X8 : $i, X9 : $i]:
% 0.19/0.56         (((k1_relat_1 @ (k7_relat_1 @ X8 @ X9))
% 0.19/0.56            = (k3_xboole_0 @ (k1_relat_1 @ X8) @ X9))
% 0.19/0.56          | ~ (v1_relat_1 @ X8))),
% 0.19/0.56      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.19/0.56  thf(t70_funct_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) =>
% 0.19/0.56         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.19/0.56  thf('18', plain,
% 0.19/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.56         (~ (r2_hidden @ X16 @ (k1_relat_1 @ (k7_relat_1 @ X17 @ X18)))
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X17 @ X18) @ X16)
% 0.19/0.56              = (k1_funct_1 @ X17 @ X16))
% 0.19/0.56          | ~ (v1_funct_1 @ X17)
% 0.19/0.56          | ~ (v1_relat_1 @ X17))),
% 0.19/0.56      inference('cnf', [status(esa)], [t70_funct_1])).
% 0.19/0.56  thf('19', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0))
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.56              = (k1_funct_1 @ X1 @ X2)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.56  thf('20', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_funct_1 @ X1 @ X2))
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.56  thf('21', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_relat_1 @ X0)
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.19/0.56              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['16', '20'])).
% 0.19/0.56  thf('22', plain,
% 0.19/0.56      (![X0 : $i]:
% 0.19/0.56         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.19/0.56            = (k1_funct_1 @ X0 @ sk_A))
% 0.19/0.56          | ((k1_funct_1 @ X0 @ sk_A) = (k1_xboole_0))
% 0.19/0.56          | ~ (v1_funct_1 @ X0)
% 0.19/0.56          | ~ (v1_relat_1 @ X0))),
% 0.19/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.56  thf('23', plain,
% 0.19/0.56      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.56         != (k1_funct_1 @ sk_C @ sk_A))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('24', plain,
% 0.19/0.56      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.19/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.56        | ((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.56  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('27', plain,
% 0.19/0.56      ((((k1_funct_1 @ sk_C @ sk_A) != (k1_funct_1 @ sk_C @ sk_A))
% 0.19/0.56        | ((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0)))),
% 0.19/0.56      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.19/0.56  thf('28', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.56  thf('29', plain,
% 0.19/0.56      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) != (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['10', '28'])).
% 0.19/0.56  thf('30', plain,
% 0.19/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.56        | ~ (v1_relat_1 @ sk_C)
% 0.19/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.56        | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['9', '29'])).
% 0.19/0.56  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('33', plain,
% 0.19/0.56      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.56        | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B)))),
% 0.19/0.56      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.19/0.56  thf('34', plain,
% 0.19/0.56      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C) @ sk_B))),
% 0.19/0.56      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.56  thf('35', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.56         (((k1_funct_1 @ (k7_relat_1 @ X1 @ X0) @ X2) = (k1_funct_1 @ X1 @ X2))
% 0.19/0.56          | ~ (v1_funct_1 @ X1)
% 0.19/0.56          | ~ (v1_relat_1 @ X1)
% 0.19/0.56          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ (k1_relat_1 @ X1) @ X0)))),
% 0.19/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.56  thf('36', plain,
% 0.19/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.19/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.19/0.56        | ((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.19/0.56            = (k1_funct_1 @ sk_C @ sk_A)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.56  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('39', plain, (((k1_funct_1 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.56  thf('40', plain,
% 0.19/0.56      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) = (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.19/0.56  thf('41', plain,
% 0.19/0.56      (((k1_funct_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A) != (k1_xboole_0))),
% 0.19/0.56      inference('demod', [status(thm)], ['10', '28'])).
% 0.19/0.56  thf('42', plain, ($false),
% 0.19/0.56      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.19/0.56  
% 0.19/0.56  % SZS output end Refutation
% 0.19/0.56  
% 0.19/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
