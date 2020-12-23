%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nyrPQi1up2

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:55 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 108 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   14
%              Number of atoms          :  506 (1064 expanded)
%              Number of equality atoms :   20 (  31 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t148_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ X11 @ ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t156_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X10 @ X8 ) @ ( k9_relat_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k9_relat_1 @ X0 @ ( k10_relat_1 @ sk_C @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k10_relat_1 @ X0 @ X1 ) )
        = ( k3_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k10_relat_1 @ X12 @ X11 ) )
        = ( k3_xboole_0 @ X11 @ ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t148_funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k9_relat_1 @ X10 @ X8 ) @ ( k9_relat_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t156_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k9_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('29',plain,
    ( ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) @ sk_A )
    = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) ) @ sk_A )
      = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['10','29'])).

thf('31',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_C ) )
    = sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('36',plain,(
    r1_tarski @ sk_A @ sk_A ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_A
    = ( k9_relat_1 @ sk_C @ ( k10_relat_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','33','38','39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['9','41','42','43','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ ( k2_relat_1 @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['1','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nyrPQi1up2
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 232 iterations in 0.173s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.39/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.62  thf(t158_funct_1, conjecture,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.62       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.39/0.62           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.39/0.62         ( r1_tarski @ A @ B ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.62        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.62          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.39/0.62              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.39/0.62            ( r1_tarski @ A @ B ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.39/0.62  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t17_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.62  thf(t146_relat_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ A ) =>
% 0.39/0.62       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X7 : $i]:
% 0.39/0.62         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.39/0.62          | ~ (v1_relat_1 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.39/0.62  thf(t148_funct_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.62       ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) =
% 0.39/0.62         ( k3_xboole_0 @ A @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) ))).
% 0.39/0.62  thf('3', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         (((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11))
% 0.39/0.62            = (k3_xboole_0 @ X11 @ (k9_relat_1 @ X12 @ (k1_relat_1 @ X12))))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.62            = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0)))
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ X0))),
% 0.39/0.62      inference('sup+', [status(thm)], ['2', '3'])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.62              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t156_relat_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ C ) =>
% 0.39/0.62       ( ( r1_tarski @ A @ B ) =>
% 0.39/0.62         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X10)
% 0.39/0.62          | (r1_tarski @ (k9_relat_1 @ X10 @ X8) @ (k9_relat_1 @ X10 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.39/0.62  thf('8', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_tarski @ (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.39/0.62           (k9_relat_1 @ X0 @ (k10_relat_1 @ sk_C @ sk_B)))
% 0.39/0.62          | ~ (v1_relat_1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.62  thf('9', plain,
% 0.39/0.62      (((r1_tarski @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ 
% 0.39/0.62         (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['5', '8'])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X0)
% 0.39/0.62          | ((k9_relat_1 @ X0 @ (k10_relat_1 @ X0 @ X1))
% 0.39/0.62              = (k3_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t28_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.39/0.62  thf('12', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('13', plain,
% 0.39/0.62      (((k3_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.39/0.62         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X11 : $i, X12 : $i]:
% 0.39/0.62         (((k9_relat_1 @ X12 @ (k10_relat_1 @ X12 @ X11))
% 0.39/0.62            = (k3_xboole_0 @ X11 @ (k9_relat_1 @ X12 @ (k1_relat_1 @ X12))))
% 0.39/0.62          | ~ (v1_funct_1 @ X12)
% 0.39/0.62          | ~ (v1_relat_1 @ X12))),
% 0.39/0.62      inference('cnf', [status(esa)], [t148_funct_1])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.62  thf('16', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r1_tarski @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X1)
% 0.39/0.62          | ~ (v1_funct_1 @ X1))),
% 0.39/0.62      inference('sup+', [status(thm)], ['14', '15'])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.62  thf('18', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X8 @ X9)
% 0.39/0.62          | ~ (v1_relat_1 @ X10)
% 0.39/0.62          | (r1_tarski @ (k9_relat_1 @ X10 @ X8) @ (k9_relat_1 @ X10 @ X9)))),
% 0.39/0.62      inference('cnf', [status(esa)], [t156_relat_1])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r1_tarski @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.39/0.62           (k9_relat_1 @ X2 @ X0))
% 0.39/0.62          | ~ (v1_relat_1 @ X2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.62  thf(t1_xboole_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.39/0.62       ( r1_tarski @ A @ C ) ))).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X2 @ X3)
% 0.39/0.62          | ~ (r1_tarski @ X3 @ X4)
% 0.39/0.62          | (r1_tarski @ X2 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.39/0.62         (~ (v1_relat_1 @ X1)
% 0.39/0.62          | (r1_tarski @ (k9_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3)
% 0.39/0.62          | ~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X3))),
% 0.39/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         (~ (v1_funct_1 @ X1)
% 0.39/0.62          | ~ (v1_relat_1 @ X1)
% 0.39/0.62          | (r1_tarski @ 
% 0.39/0.62             (k9_relat_1 @ X1 @ (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.39/0.62             X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X1))),
% 0.39/0.62      inference('sup-', [status(thm)], ['16', '21'])).
% 0.39/0.62  thf('23', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r1_tarski @ 
% 0.39/0.62           (k9_relat_1 @ X1 @ (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)) @ 
% 0.39/0.62           X0)
% 0.39/0.62          | ~ (v1_relat_1 @ X1)
% 0.39/0.62          | ~ (v1_funct_1 @ X1))),
% 0.39/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.62  thf('24', plain,
% 0.39/0.62      (((r1_tarski @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['13', '23'])).
% 0.39/0.62  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('27', plain,
% 0.39/0.62      ((r1_tarski @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.39/0.62  thf('28', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (((k3_xboole_0 @ (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)) @ sk_A)
% 0.39/0.62         = (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      ((((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) @ sk_A)
% 0.39/0.62          = (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)))
% 0.39/0.62        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_C))),
% 0.39/0.62      inference('sup+', [status(thm)], ['10', '29'])).
% 0.39/0.62  thf('31', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('33', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('34', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_C)) = (sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 0.39/0.62      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.39/0.62  thf('36', plain, ((r1_tarski @ sk_A @ sk_A)),
% 0.39/0.62      inference('sup+', [status(thm)], ['34', '35'])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X5 : $i, X6 : $i]:
% 0.39/0.62         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.39/0.62      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.39/0.62  thf('38', plain, (((k3_xboole_0 @ sk_A @ sk_A) = (sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.39/0.62  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (((sk_A) = (k9_relat_1 @ sk_C @ (k10_relat_1 @ sk_C @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '33', '38', '39', '40'])).
% 0.39/0.62  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('44', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.39/0.62      inference('demod', [status(thm)], ['9', '41', '42', '43', '44'])).
% 0.39/0.62  thf('46', plain,
% 0.39/0.62      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.39/0.62         (~ (r1_tarski @ X2 @ X3)
% 0.39/0.62          | ~ (r1_tarski @ X3 @ X4)
% 0.39/0.62          | (r1_tarski @ X2 @ X4))),
% 0.39/0.62      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((r1_tarski @ sk_A @ X0)
% 0.39/0.62          | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ (k2_relat_1 @ sk_C)) @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.39/0.62  thf('48', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.39/0.62      inference('sup-', [status(thm)], ['1', '47'])).
% 0.39/0.62  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
