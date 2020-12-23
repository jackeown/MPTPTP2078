%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nLO2j5thd6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:26 EST 2020

% Result     : Theorem 2.05s
% Output     : Refutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   77 (  93 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   22
%              Number of atoms          :  585 ( 776 expanded)
%              Number of equality atoms :   37 (  50 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(t17_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_wellord1 @ B @ A )
        = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_wellord1 @ X40 @ X39 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X39 @ X40 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('1',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_wellord1 @ X40 @ X39 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X39 @ X40 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf(t29_wellord1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
          = ( k2_wellord1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A )
            = ( k2_wellord1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_wellord1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t102_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r1_tarski @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X34 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X34 @ X32 ) @ X33 )
        = ( k7_relat_1 @ X34 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t102_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(dt_k8_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X30 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(t27_wellord1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B )
        = ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X43 @ X45 ) @ X44 )
        = ( k2_wellord1 @ ( k2_wellord1 @ X43 @ X44 ) @ X45 ) )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t27_wellord1])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) )
        & ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ) )).

thf('10',plain,(
    ! [X41: $i,X42: $i] :
      ( ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ X41 @ X42 ) ) @ X42 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t20_wellord1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X29: $i] :
      ( ( ( k3_relat_1 @ X29 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('12',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k2_tarski @ X6 @ X5 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X27 @ X28 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ X3 @ ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf(dt_k2_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','26'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('28',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X35 ) @ X36 )
      | ( ( k8_relat_1 @ X36 @ X35 )
        = X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) )
      | ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k2_wellord1 @ X0 @ sk_A ) )
        = ( k2_wellord1 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k2_wellord1 @ X40 @ X39 )
        = ( k7_relat_1 @ ( k8_relat_1 @ X39 @ X40 ) @ X39 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t17_wellord1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ( v1_relat_1 @ ( k2_wellord1 @ X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_wellord1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_wellord1 @ ( k2_wellord1 @ X0 @ sk_B ) @ sk_A )
        = ( k7_relat_1 @ ( k2_wellord1 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ( k2_wellord1 @ ( k2_wellord1 @ sk_C @ sk_B ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ( k7_relat_1 @ ( k2_wellord1 @ sk_C @ sk_A ) @ sk_B )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ( k7_relat_1 @ ( k8_relat_1 @ sk_A @ sk_C ) @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k2_wellord1 @ sk_C @ sk_A )
     != ( k2_wellord1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ( k2_wellord1 @ sk_C @ sk_A )
 != ( k2_wellord1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nLO2j5thd6
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:12:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 2.05/2.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.05/2.29  % Solved by: fo/fo7.sh
% 2.05/2.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.05/2.29  % done 1893 iterations in 1.844s
% 2.05/2.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.05/2.29  % SZS output start Refutation
% 2.05/2.29  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 2.05/2.29  thf(sk_C_type, type, sk_C: $i).
% 2.05/2.29  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.05/2.29  thf(sk_A_type, type, sk_A: $i).
% 2.05/2.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.05/2.29  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.05/2.29  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.05/2.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.05/2.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.05/2.29  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 2.05/2.29  thf(sk_B_type, type, sk_B: $i).
% 2.05/2.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.05/2.29  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.05/2.29  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 2.05/2.29  thf(t17_wellord1, axiom,
% 2.05/2.29    (![A:$i,B:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ B ) =>
% 2.05/2.29       ( ( k2_wellord1 @ B @ A ) = ( k7_relat_1 @ ( k8_relat_1 @ A @ B ) @ A ) ) ))).
% 2.05/2.29  thf('0', plain,
% 2.05/2.29      (![X39 : $i, X40 : $i]:
% 2.05/2.29         (((k2_wellord1 @ X40 @ X39)
% 2.05/2.29            = (k7_relat_1 @ (k8_relat_1 @ X39 @ X40) @ X39))
% 2.05/2.29          | ~ (v1_relat_1 @ X40))),
% 2.05/2.29      inference('cnf', [status(esa)], [t17_wellord1])).
% 2.05/2.29  thf('1', plain,
% 2.05/2.29      (![X39 : $i, X40 : $i]:
% 2.05/2.29         (((k2_wellord1 @ X40 @ X39)
% 2.05/2.29            = (k7_relat_1 @ (k8_relat_1 @ X39 @ X40) @ X39))
% 2.05/2.29          | ~ (v1_relat_1 @ X40))),
% 2.05/2.29      inference('cnf', [status(esa)], [t17_wellord1])).
% 2.05/2.29  thf(t29_wellord1, conjecture,
% 2.05/2.29    (![A:$i,B:$i,C:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ C ) =>
% 2.05/2.29       ( ( r1_tarski @ A @ B ) =>
% 2.05/2.29         ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 2.05/2.29           ( k2_wellord1 @ C @ A ) ) ) ))).
% 2.05/2.29  thf(zf_stmt_0, negated_conjecture,
% 2.05/2.29    (~( ![A:$i,B:$i,C:$i]:
% 2.05/2.29        ( ( v1_relat_1 @ C ) =>
% 2.05/2.29          ( ( r1_tarski @ A @ B ) =>
% 2.05/2.29            ( ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) =
% 2.05/2.29              ( k2_wellord1 @ C @ A ) ) ) ) )),
% 2.05/2.29    inference('cnf.neg', [status(esa)], [t29_wellord1])).
% 2.05/2.29  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.05/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.29  thf(t102_relat_1, axiom,
% 2.05/2.29    (![A:$i,B:$i,C:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ C ) =>
% 2.05/2.29       ( ( r1_tarski @ A @ B ) =>
% 2.05/2.29         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 2.05/2.29  thf('3', plain,
% 2.05/2.29      (![X32 : $i, X33 : $i, X34 : $i]:
% 2.05/2.29         (~ (r1_tarski @ X32 @ X33)
% 2.05/2.29          | ~ (v1_relat_1 @ X34)
% 2.05/2.29          | ((k7_relat_1 @ (k7_relat_1 @ X34 @ X32) @ X33)
% 2.05/2.29              = (k7_relat_1 @ X34 @ X32)))),
% 2.05/2.29      inference('cnf', [status(esa)], [t102_relat_1])).
% 2.05/2.29  thf('4', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_A) @ sk_B)
% 2.05/2.29            = (k7_relat_1 @ X0 @ sk_A))
% 2.05/2.29          | ~ (v1_relat_1 @ X0))),
% 2.05/2.29      inference('sup-', [status(thm)], ['2', '3'])).
% 2.05/2.29  thf('5', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.05/2.29            = (k7_relat_1 @ (k8_relat_1 @ sk_A @ X0) @ sk_A))
% 2.05/2.29          | ~ (v1_relat_1 @ X0)
% 2.05/2.29          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0)))),
% 2.05/2.29      inference('sup+', [status(thm)], ['1', '4'])).
% 2.05/2.29  thf(dt_k8_relat_1, axiom,
% 2.05/2.29    (![A:$i,B:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ B ) => ( v1_relat_1 @ ( k8_relat_1 @ A @ B ) ) ))).
% 2.05/2.29  thf('6', plain,
% 2.05/2.29      (![X30 : $i, X31 : $i]:
% 2.05/2.29         ((v1_relat_1 @ (k8_relat_1 @ X30 @ X31)) | ~ (v1_relat_1 @ X31))),
% 2.05/2.29      inference('cnf', [status(esa)], [dt_k8_relat_1])).
% 2.05/2.29  thf('7', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X0)
% 2.05/2.29          | ((k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.05/2.29              = (k7_relat_1 @ (k8_relat_1 @ sk_A @ X0) @ sk_A)))),
% 2.05/2.29      inference('clc', [status(thm)], ['5', '6'])).
% 2.05/2.29  thf(t27_wellord1, axiom,
% 2.05/2.29    (![A:$i,B:$i,C:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ C ) =>
% 2.05/2.29       ( ( k2_wellord1 @ ( k2_wellord1 @ C @ A ) @ B ) =
% 2.05/2.29         ( k2_wellord1 @ ( k2_wellord1 @ C @ B ) @ A ) ) ))).
% 2.05/2.29  thf('8', plain,
% 2.05/2.29      (![X43 : $i, X44 : $i, X45 : $i]:
% 2.05/2.29         (((k2_wellord1 @ (k2_wellord1 @ X43 @ X45) @ X44)
% 2.05/2.29            = (k2_wellord1 @ (k2_wellord1 @ X43 @ X44) @ X45))
% 2.05/2.29          | ~ (v1_relat_1 @ X43))),
% 2.05/2.29      inference('cnf', [status(esa)], [t27_wellord1])).
% 2.05/2.29  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 2.05/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.29  thf(t20_wellord1, axiom,
% 2.05/2.29    (![A:$i,B:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ B ) =>
% 2.05/2.29       ( ( r1_tarski @
% 2.05/2.29           ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ ( k3_relat_1 @ B ) ) & 
% 2.05/2.29         ( r1_tarski @ ( k3_relat_1 @ ( k2_wellord1 @ B @ A ) ) @ A ) ) ))).
% 2.05/2.29  thf('10', plain,
% 2.05/2.29      (![X41 : $i, X42 : $i]:
% 2.05/2.29         ((r1_tarski @ (k3_relat_1 @ (k2_wellord1 @ X41 @ X42)) @ X42)
% 2.05/2.29          | ~ (v1_relat_1 @ X41))),
% 2.05/2.29      inference('cnf', [status(esa)], [t20_wellord1])).
% 2.05/2.29  thf(d6_relat_1, axiom,
% 2.05/2.29    (![A:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ A ) =>
% 2.05/2.29       ( ( k3_relat_1 @ A ) =
% 2.05/2.29         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 2.05/2.29  thf('11', plain,
% 2.05/2.29      (![X29 : $i]:
% 2.05/2.29         (((k3_relat_1 @ X29)
% 2.05/2.29            = (k2_xboole_0 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29)))
% 2.05/2.29          | ~ (v1_relat_1 @ X29))),
% 2.05/2.29      inference('cnf', [status(esa)], [d6_relat_1])).
% 2.05/2.29  thf(commutativity_k2_tarski, axiom,
% 2.05/2.29    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 2.05/2.29  thf('12', plain,
% 2.05/2.29      (![X5 : $i, X6 : $i]: ((k2_tarski @ X6 @ X5) = (k2_tarski @ X5 @ X6))),
% 2.05/2.29      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 2.05/2.29  thf(l51_zfmisc_1, axiom,
% 2.05/2.29    (![A:$i,B:$i]:
% 2.05/2.29     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 2.05/2.29  thf('13', plain,
% 2.05/2.29      (![X27 : $i, X28 : $i]:
% 2.05/2.29         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 2.05/2.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.05/2.29  thf('14', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i]:
% 2.05/2.29         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.29      inference('sup+', [status(thm)], ['12', '13'])).
% 2.05/2.29  thf('15', plain,
% 2.05/2.29      (![X27 : $i, X28 : $i]:
% 2.05/2.29         ((k3_tarski @ (k2_tarski @ X27 @ X28)) = (k2_xboole_0 @ X27 @ X28))),
% 2.05/2.29      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 2.05/2.29  thf('16', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 2.05/2.29      inference('sup+', [status(thm)], ['14', '15'])).
% 2.05/2.29  thf(t7_xboole_1, axiom,
% 2.05/2.29    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.05/2.29  thf('17', plain,
% 2.05/2.29      (![X3 : $i, X4 : $i]: (r1_tarski @ X3 @ (k2_xboole_0 @ X3 @ X4))),
% 2.05/2.29      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.05/2.29  thf(t1_xboole_1, axiom,
% 2.05/2.29    (![A:$i,B:$i,C:$i]:
% 2.05/2.29     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 2.05/2.29       ( r1_tarski @ A @ C ) ))).
% 2.05/2.29  thf('18', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.29         (~ (r1_tarski @ X0 @ X1)
% 2.05/2.29          | ~ (r1_tarski @ X1 @ X2)
% 2.05/2.29          | (r1_tarski @ X0 @ X2))),
% 2.05/2.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.05/2.29  thf('19', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.29         ((r1_tarski @ X1 @ X2) | ~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2))),
% 2.05/2.29      inference('sup-', [status(thm)], ['17', '18'])).
% 2.05/2.29  thf('20', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.29         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X2) | (r1_tarski @ X0 @ X2))),
% 2.05/2.29      inference('sup-', [status(thm)], ['16', '19'])).
% 2.05/2.29  thf('21', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i]:
% 2.05/2.29         (~ (r1_tarski @ (k3_relat_1 @ X0) @ X1)
% 2.05/2.29          | ~ (v1_relat_1 @ X0)
% 2.05/2.29          | (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 2.05/2.29      inference('sup-', [status(thm)], ['11', '20'])).
% 2.05/2.29  thf('22', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X1)
% 2.05/2.29          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 2.05/2.29          | ~ (v1_relat_1 @ (k2_wellord1 @ X1 @ X0)))),
% 2.05/2.29      inference('sup-', [status(thm)], ['10', '21'])).
% 2.05/2.29  thf(dt_k2_wellord1, axiom,
% 2.05/2.29    (![A:$i,B:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k2_wellord1 @ A @ B ) ) ))).
% 2.05/2.29  thf('23', plain,
% 2.05/2.29      (![X37 : $i, X38 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X37) | (v1_relat_1 @ (k2_wellord1 @ X37 @ X38)))),
% 2.05/2.29      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.05/2.29  thf('24', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i]:
% 2.05/2.29         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X0)
% 2.05/2.29          | ~ (v1_relat_1 @ X1))),
% 2.05/2.29      inference('clc', [status(thm)], ['22', '23'])).
% 2.05/2.29  thf('25', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.29         (~ (r1_tarski @ X0 @ X1)
% 2.05/2.29          | ~ (r1_tarski @ X1 @ X2)
% 2.05/2.29          | (r1_tarski @ X0 @ X2))),
% 2.05/2.29      inference('cnf', [status(esa)], [t1_xboole_1])).
% 2.05/2.29  thf('26', plain,
% 2.05/2.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X1)
% 2.05/2.29          | (r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X1 @ X0)) @ X2)
% 2.05/2.29          | ~ (r1_tarski @ X0 @ X2))),
% 2.05/2.29      inference('sup-', [status(thm)], ['24', '25'])).
% 2.05/2.29  thf('27', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         ((r1_tarski @ (k2_relat_1 @ (k2_wellord1 @ X0 @ sk_A)) @ sk_B)
% 2.05/2.29          | ~ (v1_relat_1 @ X0))),
% 2.05/2.29      inference('sup-', [status(thm)], ['9', '26'])).
% 2.05/2.29  thf(t125_relat_1, axiom,
% 2.05/2.29    (![A:$i,B:$i]:
% 2.05/2.29     ( ( v1_relat_1 @ B ) =>
% 2.05/2.29       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 2.05/2.29         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 2.05/2.29  thf('28', plain,
% 2.05/2.29      (![X35 : $i, X36 : $i]:
% 2.05/2.29         (~ (r1_tarski @ (k2_relat_1 @ X35) @ X36)
% 2.05/2.29          | ((k8_relat_1 @ X36 @ X35) = (X35))
% 2.05/2.29          | ~ (v1_relat_1 @ X35))),
% 2.05/2.29      inference('cnf', [status(esa)], [t125_relat_1])).
% 2.05/2.29  thf('29', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X0)
% 2.05/2.29          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A))
% 2.05/2.29          | ((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 2.05/2.29              = (k2_wellord1 @ X0 @ sk_A)))),
% 2.05/2.29      inference('sup-', [status(thm)], ['27', '28'])).
% 2.05/2.29  thf('30', plain,
% 2.05/2.29      (![X37 : $i, X38 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X37) | (v1_relat_1 @ (k2_wellord1 @ X37 @ X38)))),
% 2.05/2.29      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.05/2.29  thf('31', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (((k8_relat_1 @ sk_B @ (k2_wellord1 @ X0 @ sk_A))
% 2.05/2.29            = (k2_wellord1 @ X0 @ sk_A))
% 2.05/2.29          | ~ (v1_relat_1 @ X0))),
% 2.05/2.29      inference('clc', [status(thm)], ['29', '30'])).
% 2.05/2.29  thf('32', plain,
% 2.05/2.29      (![X39 : $i, X40 : $i]:
% 2.05/2.29         (((k2_wellord1 @ X40 @ X39)
% 2.05/2.29            = (k7_relat_1 @ (k8_relat_1 @ X39 @ X40) @ X39))
% 2.05/2.29          | ~ (v1_relat_1 @ X40))),
% 2.05/2.29      inference('cnf', [status(esa)], [t17_wellord1])).
% 2.05/2.29  thf('33', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.05/2.29            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 2.05/2.29          | ~ (v1_relat_1 @ X0)
% 2.05/2.29          | ~ (v1_relat_1 @ (k2_wellord1 @ X0 @ sk_A)))),
% 2.05/2.29      inference('sup+', [status(thm)], ['31', '32'])).
% 2.05/2.29  thf('34', plain,
% 2.05/2.29      (![X37 : $i, X38 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X37) | (v1_relat_1 @ (k2_wellord1 @ X37 @ X38)))),
% 2.05/2.29      inference('cnf', [status(esa)], [dt_k2_wellord1])).
% 2.05/2.29  thf('35', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X0)
% 2.05/2.29          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)
% 2.05/2.29              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 2.05/2.29      inference('clc', [status(thm)], ['33', '34'])).
% 2.05/2.29  thf('36', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 2.05/2.29            = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B))
% 2.05/2.29          | ~ (v1_relat_1 @ X0)
% 2.05/2.29          | ~ (v1_relat_1 @ X0))),
% 2.05/2.29      inference('sup+', [status(thm)], ['8', '35'])).
% 2.05/2.29  thf('37', plain,
% 2.05/2.29      (![X0 : $i]:
% 2.05/2.29         (~ (v1_relat_1 @ X0)
% 2.05/2.29          | ((k2_wellord1 @ (k2_wellord1 @ X0 @ sk_B) @ sk_A)
% 2.05/2.29              = (k7_relat_1 @ (k2_wellord1 @ X0 @ sk_A) @ sk_B)))),
% 2.05/2.29      inference('simplify', [status(thm)], ['36'])).
% 2.05/2.29  thf('38', plain,
% 2.05/2.29      (((k2_wellord1 @ (k2_wellord1 @ sk_C @ sk_B) @ sk_A)
% 2.05/2.29         != (k2_wellord1 @ sk_C @ sk_A))),
% 2.05/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.29  thf('39', plain,
% 2.05/2.29      ((((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 2.05/2.29          != (k2_wellord1 @ sk_C @ sk_A))
% 2.05/2.29        | ~ (v1_relat_1 @ sk_C))),
% 2.05/2.29      inference('sup-', [status(thm)], ['37', '38'])).
% 2.05/2.29  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 2.05/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.29  thf('41', plain,
% 2.05/2.29      (((k7_relat_1 @ (k2_wellord1 @ sk_C @ sk_A) @ sk_B)
% 2.05/2.29         != (k2_wellord1 @ sk_C @ sk_A))),
% 2.05/2.29      inference('demod', [status(thm)], ['39', '40'])).
% 2.05/2.29  thf('42', plain,
% 2.05/2.29      ((((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_A)
% 2.05/2.29          != (k2_wellord1 @ sk_C @ sk_A))
% 2.05/2.29        | ~ (v1_relat_1 @ sk_C))),
% 2.05/2.29      inference('sup-', [status(thm)], ['7', '41'])).
% 2.05/2.29  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 2.05/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.29  thf('44', plain,
% 2.05/2.29      (((k7_relat_1 @ (k8_relat_1 @ sk_A @ sk_C) @ sk_A)
% 2.05/2.29         != (k2_wellord1 @ sk_C @ sk_A))),
% 2.05/2.29      inference('demod', [status(thm)], ['42', '43'])).
% 2.05/2.29  thf('45', plain,
% 2.05/2.29      ((((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))
% 2.05/2.29        | ~ (v1_relat_1 @ sk_C))),
% 2.05/2.29      inference('sup-', [status(thm)], ['0', '44'])).
% 2.05/2.29  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 2.05/2.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.05/2.29  thf('47', plain,
% 2.05/2.29      (((k2_wellord1 @ sk_C @ sk_A) != (k2_wellord1 @ sk_C @ sk_A))),
% 2.05/2.29      inference('demod', [status(thm)], ['45', '46'])).
% 2.05/2.29  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 2.05/2.29  
% 2.05/2.29  % SZS output end Refutation
% 2.05/2.29  
% 2.05/2.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
