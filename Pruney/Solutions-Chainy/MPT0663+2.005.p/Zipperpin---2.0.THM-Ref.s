%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LbKNeRYi19

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:48 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 114 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   13
%              Number of atoms          :  528 ( 980 expanded)
%              Number of equality atoms :   40 (  74 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
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
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X29 @ X30 ) )
      = ( k3_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ X37 @ X36 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X36 ) @ X37 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t43_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ X47 ) @ ( k6_relat_1 @ X46 ) )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X46 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t43_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
        = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X1 ) @ X0 )
      = ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ ( k1_relat_1 @ ( k7_relat_1 @ X35 @ X34 ) ) )
      | ( r2_hidden @ X33 @ ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('15',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('16',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('17',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X31: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X31 ) )
      = X31 ) ),
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

thf('21',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_relat_1 @ X40 )
      | ~ ( v1_funct_1 @ X40 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ X41 @ X40 ) @ X42 )
        = ( k1_funct_1 @ X40 @ ( k1_funct_1 @ X41 @ X42 ) ) )
      | ~ ( r2_hidden @ X42 @ ( k1_relat_1 @ X41 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t23_funct_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('24',plain,(
    ! [X39: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ X1 )
        = ( k1_funct_1 @ X2 @ ( k1_funct_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['7','18'])).

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

thf('28',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X44
       != ( k6_relat_1 @ X43 ) )
      | ( ( k1_funct_1 @ X44 @ X45 )
        = X45 )
      | ~ ( r2_hidden @ X45 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('29',plain,(
    ! [X43: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X43 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X43 ) )
      | ~ ( r2_hidden @ X45 @ X43 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X43 ) @ X45 )
        = X45 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X38: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('31',plain,(
    ! [X39: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('32',plain,(
    ! [X43: $i,X45: $i] :
      ( ~ ( r2_hidden @ X45 @ X43 )
      | ( ( k1_funct_1 @ ( k6_relat_1 @ X43 ) @ X45 )
        = X45 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( k1_funct_1 @ ( k6_relat_1 @ sk_B ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_funct_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ X0 ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ sk_A )
        = ( k1_funct_1 @ X0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k1_funct_1 @ ( k7_relat_1 @ sk_C_1 @ sk_B ) @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ sk_A )
     != ( k1_funct_1 @ sk_C_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k1_funct_1 @ sk_C_1 @ sk_A )
 != ( k1_funct_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    $false ),
    inference(simplify,[status(thm)],['41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LbKNeRYi19
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:42:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.10/1.30  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.10/1.30  % Solved by: fo/fo7.sh
% 1.10/1.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.10/1.30  % done 1114 iterations in 0.845s
% 1.10/1.30  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.10/1.30  % SZS output start Refutation
% 1.10/1.30  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.10/1.30  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.10/1.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.10/1.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.10/1.30  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.10/1.30  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.10/1.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.10/1.30  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 1.10/1.30  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.10/1.30  thf(sk_B_type, type, sk_B: $i).
% 1.10/1.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.10/1.30  thf(sk_A_type, type, sk_A: $i).
% 1.10/1.30  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.10/1.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.10/1.30  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.10/1.30  thf(t94_relat_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( v1_relat_1 @ B ) =>
% 1.10/1.30       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 1.10/1.30  thf('0', plain,
% 1.10/1.30      (![X36 : $i, X37 : $i]:
% 1.10/1.30         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 1.10/1.30          | ~ (v1_relat_1 @ X37))),
% 1.10/1.30      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.10/1.30  thf(t71_funct_1, conjecture,
% 1.10/1.30    (![A:$i,B:$i,C:$i]:
% 1.10/1.30     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.10/1.30       ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 1.10/1.30         ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k1_funct_1 @ C @ A ) ) ) ))).
% 1.10/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.10/1.30    (~( ![A:$i,B:$i,C:$i]:
% 1.10/1.30        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.10/1.30          ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k1_relat_1 @ C ) @ B ) ) =>
% 1.10/1.30            ( ( k1_funct_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 1.10/1.30              ( k1_funct_1 @ C @ A ) ) ) ) )),
% 1.10/1.30    inference('cnf.neg', [status(esa)], [t71_funct_1])).
% 1.10/1.30  thf('1', plain,
% 1.10/1.30      ((r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_relat_1 @ sk_C_1) @ sk_B))),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf(commutativity_k2_tarski, axiom,
% 1.10/1.30    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.10/1.30  thf('2', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]: ((k2_tarski @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 1.10/1.30      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.10/1.30  thf(t12_setfam_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.10/1.30  thf('3', plain,
% 1.10/1.30      (![X29 : $i, X30 : $i]:
% 1.10/1.30         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.10/1.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.10/1.30  thf('4', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]:
% 1.10/1.30         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 1.10/1.30      inference('sup+', [status(thm)], ['2', '3'])).
% 1.10/1.30  thf('5', plain,
% 1.10/1.30      (![X29 : $i, X30 : $i]:
% 1.10/1.30         ((k1_setfam_1 @ (k2_tarski @ X29 @ X30)) = (k3_xboole_0 @ X29 @ X30))),
% 1.10/1.30      inference('cnf', [status(esa)], [t12_setfam_1])).
% 1.10/1.30  thf('6', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.10/1.30      inference('sup+', [status(thm)], ['4', '5'])).
% 1.10/1.30  thf('7', plain,
% 1.10/1.30      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_relat_1 @ sk_C_1)))),
% 1.10/1.30      inference('demod', [status(thm)], ['1', '6'])).
% 1.10/1.30  thf('8', plain,
% 1.10/1.30      (![X36 : $i, X37 : $i]:
% 1.10/1.30         (((k7_relat_1 @ X37 @ X36) = (k5_relat_1 @ (k6_relat_1 @ X36) @ X37))
% 1.10/1.30          | ~ (v1_relat_1 @ X37))),
% 1.10/1.30      inference('cnf', [status(esa)], [t94_relat_1])).
% 1.10/1.30  thf(t43_funct_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( k5_relat_1 @ ( k6_relat_1 @ B ) @ ( k6_relat_1 @ A ) ) =
% 1.10/1.30       ( k6_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.10/1.30  thf('9', plain,
% 1.10/1.30      (![X46 : $i, X47 : $i]:
% 1.10/1.30         ((k5_relat_1 @ (k6_relat_1 @ X47) @ (k6_relat_1 @ X46))
% 1.10/1.30           = (k6_relat_1 @ (k3_xboole_0 @ X46 @ X47)))),
% 1.10/1.30      inference('cnf', [status(esa)], [t43_funct_1])).
% 1.10/1.30  thf('10', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]:
% 1.10/1.30         (((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.10/1.30            = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))
% 1.10/1.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X1)))),
% 1.10/1.30      inference('sup+', [status(thm)], ['8', '9'])).
% 1.10/1.30  thf(fc3_funct_1, axiom,
% 1.10/1.30    (![A:$i]:
% 1.10/1.30     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.10/1.30       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.10/1.30  thf('11', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 1.10/1.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.10/1.30  thf('12', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i]:
% 1.10/1.30         ((k7_relat_1 @ (k6_relat_1 @ X1) @ X0)
% 1.10/1.30           = (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.10/1.30      inference('demod', [status(thm)], ['10', '11'])).
% 1.10/1.30  thf(t86_relat_1, axiom,
% 1.10/1.30    (![A:$i,B:$i,C:$i]:
% 1.10/1.30     ( ( v1_relat_1 @ C ) =>
% 1.10/1.30       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 1.10/1.30         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 1.10/1.30  thf('13', plain,
% 1.10/1.30      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X33 @ (k1_relat_1 @ (k7_relat_1 @ X35 @ X34)))
% 1.10/1.30          | (r2_hidden @ X33 @ (k1_relat_1 @ X35))
% 1.10/1.30          | ~ (v1_relat_1 @ X35))),
% 1.10/1.30      inference('cnf', [status(esa)], [t86_relat_1])).
% 1.10/1.30  thf('14', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X2 @ 
% 1.10/1.30             (k1_relat_1 @ (k6_relat_1 @ (k3_xboole_0 @ X1 @ X0))))
% 1.10/1.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 1.10/1.30          | (r2_hidden @ X2 @ (k1_relat_1 @ (k6_relat_1 @ X1))))),
% 1.10/1.30      inference('sup-', [status(thm)], ['12', '13'])).
% 1.10/1.30  thf(t71_relat_1, axiom,
% 1.10/1.30    (![A:$i]:
% 1.10/1.30     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 1.10/1.30       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 1.10/1.30  thf('15', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 1.10/1.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.10/1.30  thf('16', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 1.10/1.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.10/1.30  thf('17', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 1.10/1.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.10/1.30  thf('18', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 1.10/1.30      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.10/1.30  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.10/1.30      inference('sup-', [status(thm)], ['7', '18'])).
% 1.10/1.30  thf('20', plain, (![X31 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X31)) = (X31))),
% 1.10/1.30      inference('cnf', [status(esa)], [t71_relat_1])).
% 1.10/1.30  thf(t23_funct_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.10/1.30       ( ![C:$i]:
% 1.10/1.30         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.10/1.30           ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 1.10/1.30             ( ( k1_funct_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 1.10/1.30               ( k1_funct_1 @ C @ ( k1_funct_1 @ B @ A ) ) ) ) ) ) ))).
% 1.10/1.30  thf('21', plain,
% 1.10/1.30      (![X40 : $i, X41 : $i, X42 : $i]:
% 1.10/1.30         (~ (v1_relat_1 @ X40)
% 1.10/1.30          | ~ (v1_funct_1 @ X40)
% 1.10/1.30          | ((k1_funct_1 @ (k5_relat_1 @ X41 @ X40) @ X42)
% 1.10/1.30              = (k1_funct_1 @ X40 @ (k1_funct_1 @ X41 @ X42)))
% 1.10/1.30          | ~ (r2_hidden @ X42 @ (k1_relat_1 @ X41))
% 1.10/1.30          | ~ (v1_funct_1 @ X41)
% 1.10/1.30          | ~ (v1_relat_1 @ X41))),
% 1.10/1.30      inference('cnf', [status(esa)], [t23_funct_1])).
% 1.10/1.30  thf('22', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X1 @ X0)
% 1.10/1.30          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 1.10/1.30          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 1.10/1.30          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 1.10/1.30              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.10/1.30          | ~ (v1_funct_1 @ X2)
% 1.10/1.30          | ~ (v1_relat_1 @ X2))),
% 1.10/1.30      inference('sup-', [status(thm)], ['20', '21'])).
% 1.10/1.30  thf('23', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 1.10/1.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.10/1.30  thf('24', plain, (![X39 : $i]: (v1_funct_1 @ (k6_relat_1 @ X39))),
% 1.10/1.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.10/1.30  thf('25', plain,
% 1.10/1.30      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X1 @ X0)
% 1.10/1.30          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ X0) @ X2) @ X1)
% 1.10/1.30              = (k1_funct_1 @ X2 @ (k1_funct_1 @ (k6_relat_1 @ X0) @ X1)))
% 1.10/1.30          | ~ (v1_funct_1 @ X2)
% 1.10/1.30          | ~ (v1_relat_1 @ X2))),
% 1.10/1.30      inference('demod', [status(thm)], ['22', '23', '24'])).
% 1.10/1.30  thf('26', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         (~ (v1_relat_1 @ X0)
% 1.10/1.30          | ~ (v1_funct_1 @ X0)
% 1.10/1.30          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 1.10/1.30              = (k1_funct_1 @ X0 @ (k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A))))),
% 1.10/1.30      inference('sup-', [status(thm)], ['19', '25'])).
% 1.10/1.30  thf('27', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.10/1.30      inference('sup-', [status(thm)], ['7', '18'])).
% 1.10/1.30  thf(t34_funct_1, axiom,
% 1.10/1.30    (![A:$i,B:$i]:
% 1.10/1.30     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.10/1.30       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 1.10/1.30         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 1.10/1.30           ( ![C:$i]:
% 1.10/1.30             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 1.10/1.30  thf('28', plain,
% 1.10/1.30      (![X43 : $i, X44 : $i, X45 : $i]:
% 1.10/1.30         (((X44) != (k6_relat_1 @ X43))
% 1.10/1.30          | ((k1_funct_1 @ X44 @ X45) = (X45))
% 1.10/1.30          | ~ (r2_hidden @ X45 @ X43)
% 1.10/1.30          | ~ (v1_funct_1 @ X44)
% 1.10/1.30          | ~ (v1_relat_1 @ X44))),
% 1.10/1.30      inference('cnf', [status(esa)], [t34_funct_1])).
% 1.10/1.30  thf('29', plain,
% 1.10/1.30      (![X43 : $i, X45 : $i]:
% 1.10/1.30         (~ (v1_relat_1 @ (k6_relat_1 @ X43))
% 1.10/1.30          | ~ (v1_funct_1 @ (k6_relat_1 @ X43))
% 1.10/1.30          | ~ (r2_hidden @ X45 @ X43)
% 1.10/1.30          | ((k1_funct_1 @ (k6_relat_1 @ X43) @ X45) = (X45)))),
% 1.10/1.30      inference('simplify', [status(thm)], ['28'])).
% 1.10/1.30  thf('30', plain, (![X38 : $i]: (v1_relat_1 @ (k6_relat_1 @ X38))),
% 1.10/1.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.10/1.30  thf('31', plain, (![X39 : $i]: (v1_funct_1 @ (k6_relat_1 @ X39))),
% 1.10/1.30      inference('cnf', [status(esa)], [fc3_funct_1])).
% 1.10/1.30  thf('32', plain,
% 1.10/1.30      (![X43 : $i, X45 : $i]:
% 1.10/1.30         (~ (r2_hidden @ X45 @ X43)
% 1.10/1.30          | ((k1_funct_1 @ (k6_relat_1 @ X43) @ X45) = (X45)))),
% 1.10/1.30      inference('demod', [status(thm)], ['29', '30', '31'])).
% 1.10/1.30  thf('33', plain, (((k1_funct_1 @ (k6_relat_1 @ sk_B) @ sk_A) = (sk_A))),
% 1.10/1.30      inference('sup-', [status(thm)], ['27', '32'])).
% 1.10/1.30  thf('34', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         (~ (v1_relat_1 @ X0)
% 1.10/1.30          | ~ (v1_funct_1 @ X0)
% 1.10/1.30          | ((k1_funct_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_B) @ X0) @ sk_A)
% 1.10/1.30              = (k1_funct_1 @ X0 @ sk_A)))),
% 1.10/1.30      inference('demod', [status(thm)], ['26', '33'])).
% 1.10/1.30  thf('35', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         (((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 1.10/1.30            = (k1_funct_1 @ X0 @ sk_A))
% 1.10/1.30          | ~ (v1_relat_1 @ X0)
% 1.10/1.30          | ~ (v1_funct_1 @ X0)
% 1.10/1.30          | ~ (v1_relat_1 @ X0))),
% 1.10/1.30      inference('sup+', [status(thm)], ['0', '34'])).
% 1.10/1.30  thf('36', plain,
% 1.10/1.30      (![X0 : $i]:
% 1.10/1.30         (~ (v1_funct_1 @ X0)
% 1.10/1.30          | ~ (v1_relat_1 @ X0)
% 1.10/1.30          | ((k1_funct_1 @ (k7_relat_1 @ X0 @ sk_B) @ sk_A)
% 1.10/1.30              = (k1_funct_1 @ X0 @ sk_A)))),
% 1.10/1.30      inference('simplify', [status(thm)], ['35'])).
% 1.10/1.30  thf('37', plain,
% 1.10/1.30      (((k1_funct_1 @ (k7_relat_1 @ sk_C_1 @ sk_B) @ sk_A)
% 1.10/1.30         != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf('38', plain,
% 1.10/1.30      ((((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))
% 1.10/1.30        | ~ (v1_relat_1 @ sk_C_1)
% 1.10/1.30        | ~ (v1_funct_1 @ sk_C_1))),
% 1.10/1.30      inference('sup-', [status(thm)], ['36', '37'])).
% 1.10/1.30  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf('40', plain, ((v1_funct_1 @ sk_C_1)),
% 1.10/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.10/1.30  thf('41', plain,
% 1.10/1.30      (((k1_funct_1 @ sk_C_1 @ sk_A) != (k1_funct_1 @ sk_C_1 @ sk_A))),
% 1.10/1.30      inference('demod', [status(thm)], ['38', '39', '40'])).
% 1.10/1.30  thf('42', plain, ($false), inference('simplify', [status(thm)], ['41'])).
% 1.10/1.30  
% 1.10/1.30  % SZS output end Refutation
% 1.10/1.30  
% 1.10/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
