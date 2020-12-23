%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mi84hN9xZ2

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:05 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 148 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   22
%              Number of atoms          :  527 (1066 expanded)
%              Number of equality atoms :   37 (  51 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t214_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t214_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X53 @ X52 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X53 ) @ ( k1_relat_1 @ X52 ) ) )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t14_relat_1])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ X0 ) ),
    inference(demod,[status(thm)],['8','11','12','13'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X18 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('16',plain,
    ( ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( r1_xboole_0 @ X26 @ ( k3_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 ) @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) @ ( k1_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X48 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ ( k3_xboole_0 @ k1_xboole_0 @ sk_A ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40','43','44','45'])).

thf('47',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X18 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('48',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t196_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( ( ( k1_relat_1 @ A )
                = k1_xboole_0 )
              & ( ( k1_relat_1 @ B )
                = k1_xboole_0 ) )
           => ( A = B ) ) ) ) )).

thf('49',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( X55 = X54 )
      | ( ( k1_relat_1 @ X54 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X55 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t196_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','33'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','53'])).

thf('55',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k3_xboole_0 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Mi84hN9xZ2
% 0.15/0.38  % Computer   : n013.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:58:10 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.24/0.39  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 365 iterations in 0.091s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.58  thf(t214_relat_1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( v1_relat_1 @ B ) =>
% 0.37/0.58           ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.58             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( v1_relat_1 @ A ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( v1_relat_1 @ B ) =>
% 0.37/0.58              ( ( r1_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.58                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t214_relat_1])).
% 0.37/0.58  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(fc1_relat_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (![X48 : $i, X49 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X48) | (v1_relat_1 @ (k3_xboole_0 @ X48 @ X49)))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.37/0.58  thf('2', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d7_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.37/0.58       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (((k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 0.37/0.58         = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.58  thf(t14_relat_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( v1_relat_1 @ B ) =>
% 0.37/0.58           ( r1_tarski @
% 0.37/0.58             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.37/0.58             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (![X52 : $i, X53 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X52)
% 0.37/0.58          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X53 @ X52)) @ 
% 0.37/0.58             (k3_xboole_0 @ (k1_relat_1 @ X53) @ (k1_relat_1 @ X52)))
% 0.37/0.58          | ~ (v1_relat_1 @ X53))),
% 0.37/0.58      inference('cnf', [status(esa)], [t14_relat_1])).
% 0.37/0.58  thf(t63_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.37/0.58       ( r1_xboole_0 @ A @ C ) ))).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.37/0.58         (~ (r1_tarski @ X13 @ X14)
% 0.37/0.58          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.37/0.58          | (r1_xboole_0 @ X13 @ X15))),
% 0.37/0.58      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.37/0.58          | ~ (r1_xboole_0 @ 
% 0.37/0.58               (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)) @ X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ sk_B)
% 0.37/0.58          | ~ (v1_relat_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.37/0.58  thf('9', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.58  thf(symmetry_r1_xboole_0, axiom,
% 0.37/0.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.58  thf('11', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ X0)),
% 0.37/0.58      inference('demod', [status(thm)], ['8', '11', '12', '13'])).
% 0.37/0.58  thf(t66_xboole_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.37/0.58       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X18 : $i]: (((X18) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X18 @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (((k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.58  thf('17', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.37/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf('20', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(t74_xboole_1, axiom,
% 0.37/0.58    (![A:$i,B:$i,C:$i]:
% 0.37/0.58     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.37/0.58          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ X26 @ X27)
% 0.37/0.58          | (r1_xboole_0 @ X26 @ (k3_xboole_0 @ X27 @ X28)))),
% 0.37/0.58      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_xboole_0 @ (k1_relat_1 @ sk_A) @ 
% 0.37/0.58          (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      (![X3 : $i, X4 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.37/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (r1_xboole_0 @ (k3_xboole_0 @ (k1_relat_1 @ sk_B) @ X0) @ 
% 0.37/0.58          (k1_relat_1 @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.37/0.58          | ~ (r1_xboole_0 @ 
% 0.37/0.58               (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)) @ X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 0.37/0.58           (k1_relat_1 @ sk_A))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ~ (v1_relat_1 @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.58  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('28', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ sk_B @ X0)) @ 
% 0.37/0.58           (k1_relat_1 @ sk_A))
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('demod', [status(thm)], ['26', '27'])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (((r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ sk_A))
% 0.37/0.58        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['19', '28'])).
% 0.37/0.58  thf('30', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      (![X48 : $i, X49 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X48) | (v1_relat_1 @ (k3_xboole_0 @ X48 @ X49)))),
% 0.37/0.58      inference('cnf', [status(esa)], [fc1_relat_1])).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X0 : $i]: ((v1_relat_1 @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('sup+', [status(thm)], ['31', '32'])).
% 0.37/0.58  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.37/0.58  thf('35', plain,
% 0.37/0.58      ((r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['29', '34'])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (((k3_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ sk_A))
% 0.37/0.58         = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X1)
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.37/0.58          | ~ (r1_xboole_0 @ 
% 0.37/0.58               (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)) @ X2))),
% 0.37/0.58      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.37/0.58          | (r1_xboole_0 @ (k1_relat_1 @ (k3_xboole_0 @ k1_xboole_0 @ sk_A)) @ 
% 0.37/0.58             X0)
% 0.37/0.58          | ~ (v1_relat_1 @ sk_A)
% 0.37/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.37/0.58  thf('40', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['41', '42'])).
% 0.37/0.58  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X0 : $i]: (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.37/0.58      inference('demod', [status(thm)], ['39', '40', '43', '44', '45'])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      (![X18 : $i]: (((X18) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X18 @ X18))),
% 0.37/0.58      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.37/0.58  thf('48', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['46', '47'])).
% 0.37/0.58  thf(t196_relat_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( v1_relat_1 @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( v1_relat_1 @ B ) =>
% 0.37/0.58           ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.58               ( ( k1_relat_1 @ B ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.58             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      (![X54 : $i, X55 : $i]:
% 0.37/0.58         (~ (v1_relat_1 @ X54)
% 0.37/0.58          | ((X55) = (X54))
% 0.37/0.58          | ((k1_relat_1 @ X54) != (k1_xboole_0))
% 0.37/0.58          | ((k1_relat_1 @ X55) != (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X55))),
% 0.37/0.58      inference('cnf', [status(esa)], [t196_relat_1])).
% 0.37/0.58  thf('50', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.58          | ((X0) = (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.37/0.58  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.37/0.58      inference('sup-', [status(thm)], ['30', '33'])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0)
% 0.37/0.58          | ((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.58          | ((X0) = (k1_xboole_0)))),
% 0.37/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (![X0 : $i]:
% 0.37/0.58         (((X0) = (k1_xboole_0))
% 0.37/0.58          | ((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.37/0.58          | ~ (v1_relat_1 @ X0))),
% 0.37/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      ((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.58        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.37/0.58        | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['16', '53'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      ((((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.37/0.58        | ~ (v1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.37/0.58      inference('simplify', [status(thm)], ['54'])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      ((~ (v1_relat_1 @ sk_A) | ((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['1', '55'])).
% 0.37/0.58  thf('57', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('58', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.37/0.58      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.58  thf('59', plain,
% 0.37/0.58      (![X0 : $i, X2 : $i]:
% 0.37/0.58         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.37/0.58  thf('61', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.37/0.58      inference('simplify', [status(thm)], ['60'])).
% 0.37/0.58  thf('62', plain, ($false), inference('demod', [status(thm)], ['0', '61'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
