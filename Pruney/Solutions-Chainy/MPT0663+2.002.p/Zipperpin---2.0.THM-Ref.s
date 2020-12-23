%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TSbI47kCLu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:48 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   62 (  89 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  447 ( 734 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k7_relat_1 @ X40 @ X39 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X39 ) @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t71_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
       => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k1_funct_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) )
         => ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k1_funct_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t71_funct_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X35 @ X36 ) )
      = ( k3_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('12',plain,(
    ! [X37: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t23_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
           => ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A )
              = ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X44 @ X43 ) @ X45 )
        = ( k1_funct_1 @ X43 @ ( k1_funct_1 @ X44 @ X45 ) ) )
      | ~ ( r2_hidden @ X45 @ ( k1_relat_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('16',plain,(
    ! [X42: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( X47
       != ( k6_relat_1 @ X46 ) )
      | ( ( k1_funct_1 @ X47 @ X48 )
        = X48 )
      | ~ ( r2_hidden @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('21',plain,(
    ! [X46: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X46 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X46 ) )
      | ~ ( r2_hidden @ X48 @ X46 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X46 ) @ X48 )
        = X48 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X41: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('23',plain,(
    ! [X42: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X46: $i,X48: $i] :
      ( ~ ( r2_hidden @ X48 @ X46 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X46 ) @ X48 )
        = X48 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C_2 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ sk_A )
     != ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ( k1_funct_1 @ sk_C_2 @ sk_A )
 != ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TSbI47kCLu
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:07:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.54  % Solved by: fo/fo7.sh
% 0.19/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.54  % done 171 iterations in 0.091s
% 0.19/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.54  % SZS output start Refutation
% 0.19/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.54  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.19/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.54  thf(t94_relat_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( v1_relat_1 @ B ) =>
% 0.19/0.54       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.19/0.54  thf('0', plain,
% 0.19/0.54      (![X39 : $i, X40 : $i]:
% 0.19/0.54         (((k7_relat_1 @ X40 @ X39) = (k5_relat_1 @ (k6_relat_1 @ X39) @ X40))
% 0.19/0.54          | ~ (v1_relat_1 @ X40))),
% 0.19/0.54      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.19/0.54  thf(t71_funct_1, conjecture,
% 0.19/0.54    (![A:$i,B:$i,C:$i]:
% 0.19/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.54       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.19/0.54         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 0.19/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.54        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.54          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 0.19/0.54            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.19/0.54              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 0.19/0.54    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 0.19/0.54  thf('1', plain,
% 0.19/0.54      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf(commutativity_k2_tarski, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.54  thf('2', plain,
% 0.19/0.54      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.19/0.54      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.54  thf(t12_setfam_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.54  thf('3', plain,
% 0.19/0.54      (![X35 : $i, X36 : $i]:
% 0.19/0.54         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.19/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.54  thf('4', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]:
% 0.19/0.54         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('sup+', [status(thm)], ['2', '3'])).
% 0.19/0.54  thf('5', plain,
% 0.19/0.54      (![X35 : $i, X36 : $i]:
% 0.19/0.54         ((k1_setfam_1 @ (k2_tarski @ X35 @ X36)) = (k3_xboole_0 @ X35 @ X36))),
% 0.19/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.54  thf('6', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.19/0.54  thf('7', plain,
% 0.19/0.54      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_2)))),
% 0.19/0.54      inference('demod', [status(thm)], ['1', '6'])).
% 0.19/0.54  thf(t17_xboole_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.19/0.54  thf('8', plain,
% 0.19/0.54      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.19/0.54      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.19/0.54  thf(d3_tarski, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.54  thf('9', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.54          | (r2_hidden @ X0 @ X2)
% 0.19/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.54  thf('10', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.19/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.54  thf('11', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.54  thf(t71_relat_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.54       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.54  thf('12', plain, (![X37 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X37)) = (X37))),
% 0.19/0.54      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.54  thf(t23_funct_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.54       ( ![C:$i]:
% 0.19/0.54         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.54           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.54             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.19/0.54               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 0.19/0.54  thf('13', plain,
% 0.19/0.54      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X43)
% 0.19/0.54          | ~ (v1_funct_1 @ X43)
% 0.19/0.54          | ((k1_funct_1 @ (k5_relat_1 @ X44 @ X43) @ X45)
% 0.19/0.54              = (k1_funct_1 @ X43 @ (k1_funct_1 @ X44 @ X45)))
% 0.19/0.54          | ~ (r2_hidden @ X45 @ (k1_relat_1 @ X44))
% 0.19/0.54          | ~ (v1_funct_1 @ X44)
% 0.19/0.54          | ~ (v1_relat_1 @ X44))),
% 0.19/0.54      inference('cnf', [status(esa)], [t23_funct_1])).
% 0.19/0.54  thf('14', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.54          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.19/0.54          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.19/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.19/0.54              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.19/0.54          | ~ (v1_funct_1 @ X2)
% 0.19/0.54          | ~ (v1_relat_1 @ X2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.54  thf(fc3_funct_1, axiom,
% 0.19/0.54    (![A:$i]:
% 0.19/0.54     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.19/0.54       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.19/0.54  thf('15', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('16', plain, (![X42 : $i]: (v1_funct_1 @ (k6_relat_1 @ X42))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('17', plain,
% 0.19/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X1 @ X0)
% 0.19/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 0.19/0.54              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 0.19/0.54          | ~ (v1_funct_1 @ X2)
% 0.19/0.54          | ~ (v1_relat_1 @ X2))),
% 0.19/0.54      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.19/0.54  thf('18', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X0)
% 0.19/0.54          | ~ (v1_funct_1 @ X0)
% 0.19/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.19/0.54              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 0.19/0.54      inference('sup-', [status(thm)], ['11', '17'])).
% 0.19/0.54  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.54      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.54  thf(t34_funct_1, axiom,
% 0.19/0.54    (![A:$i,B:$i]:
% 0.19/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.54       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.19/0.54         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.54           ( ![C:$i]:
% 0.19/0.54             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.19/0.54  thf('20', plain,
% 0.19/0.54      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.19/0.54         (((X47) != (k6_relat_1 @ X46))
% 0.19/0.54          | ((k1_funct_1 @ X47 @ X48) = (X48))
% 0.19/0.54          | ~ (r2_hidden @ X48 @ X46)
% 0.19/0.54          | ~ (v1_funct_1 @ X47)
% 0.19/0.54          | ~ (v1_relat_1 @ X47))),
% 0.19/0.54      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.19/0.54  thf('21', plain,
% 0.19/0.54      (![X46 : $i, X48 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ (k6_relat_1 @ X46))
% 0.19/0.54          | ~ (v1_funct_1 @ (k6_relat_1 @ X46))
% 0.19/0.54          | ~ (r2_hidden @ X48 @ X46)
% 0.19/0.54          | ((k1_funct_1 @ (k6_relat_1 @ X46) @ X48) = (X48)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.54  thf('22', plain, (![X41 : $i]: (v1_relat_1 @ (k6_relat_1 @ X41))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('23', plain, (![X42 : $i]: (v1_funct_1 @ (k6_relat_1 @ X42))),
% 0.19/0.54      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.19/0.54  thf('24', plain,
% 0.19/0.54      (![X46 : $i, X48 : $i]:
% 0.19/0.54         (~ (r2_hidden @ X48 @ X46)
% 0.19/0.54          | ((k1_funct_1 @ (k6_relat_1 @ X46) @ X48) = (X48)))),
% 0.19/0.54      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.19/0.54  thf('25', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 0.19/0.54      inference('sup-', [status(thm)], ['19', '24'])).
% 0.19/0.54  thf('26', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (v1_relat_1 @ X0)
% 0.19/0.54          | ~ (v1_funct_1 @ X0)
% 0.19/0.54          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.19/0.54              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.19/0.54      inference('demod', [status(thm)], ['18', '25'])).
% 0.19/0.54  thf('27', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.19/0.54            = (k1_funct_1 @ X0 @ sk_A))
% 0.19/0.54          | ~ (v1_relat_1 @ X0)
% 0.19/0.54          | ~ (v1_funct_1 @ X0)
% 0.19/0.54          | ~ (v1_relat_1 @ X0))),
% 0.19/0.54      inference('sup+', [status(thm)], ['0', '26'])).
% 0.19/0.54  thf('28', plain,
% 0.19/0.54      (![X0 : $i]:
% 0.19/0.54         (~ (v1_funct_1 @ X0)
% 0.19/0.54          | ~ (v1_relat_1 @ X0)
% 0.19/0.54          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 0.19/0.54              = (k1_funct_1 @ X0 @ sk_A)))),
% 0.19/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.54  thf('29', plain,
% 0.19/0.54      (((k1_funct_1 @ (k7_relat_1 @ sk_C_2 @ sk_B) @ sk_A)
% 0.19/0.54         != (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('30', plain,
% 0.19/0.54      ((((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.19/0.54        | ~ (v1_relat_1 @ sk_C_2)
% 0.19/0.54        | ~ (v1_funct_1 @ sk_C_2))),
% 0.19/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.54  thf('31', plain, ((v1_relat_1 @ sk_C_2)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('32', plain, ((v1_funct_1 @ sk_C_2)),
% 0.19/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.54  thf('33', plain,
% 0.19/0.54      (((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.19/0.54      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.19/0.54  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.19/0.54  
% 0.19/0.54  % SZS output end Refutation
% 0.19/0.54  
% 0.19/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
