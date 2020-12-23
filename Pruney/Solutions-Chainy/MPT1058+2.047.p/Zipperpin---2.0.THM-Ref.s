%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SOMTxx1zbe

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:43 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :   20
%              Number of atoms          :  683 (1250 expanded)
%              Number of equality atoms :   45 (  82 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t175_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
         => ( ( k10_relat_1 @ A @ C )
            = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B )
           => ( ( k10_relat_1 @ A @ C )
              = ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t175_funct_2])).

thf('1',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_A @ sk_C ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t103_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r1_tarski @ X38 @ X39 )
      | ~ ( v1_relat_1 @ X40 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X40 @ X39 ) @ X38 )
        = ( k7_relat_1 @ X40 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t103_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('6',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) @ X37 )
        = ( k7_relat_1 @ X35 @ ( k3_xboole_0 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('9',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X42 @ X41 ) @ X43 )
        = ( k3_xboole_0 @ X41 @ ( k10_relat_1 @ X42 @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X3 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X3 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X3 ) ) ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 )
        = ( k3_xboole_0 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('17',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) @ X37 )
        = ( k7_relat_1 @ X35 @ ( k3_xboole_0 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X35 @ X36 ) @ X37 )
        = ( k7_relat_1 @ X35 @ ( k3_xboole_0 @ X36 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( v1_relat_1 @ X33 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_B @ ( k10_relat_1 @ sk_A @ sk_C ) ) ) ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k10_relat_1 @ sk_A @ sk_C ) )
        = ( k7_relat_1 @ X0 @ ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_C )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ ( k10_relat_1 @ sk_A @ sk_C ) ) @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k3_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_C ) @ ( k10_relat_1 @ sk_A @ sk_C ) )
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('44',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( k10_relat_1 @ sk_A @ sk_C )
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ( k10_relat_1 @ sk_A @ sk_C )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SOMTxx1zbe
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:09:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 307 iterations in 0.283s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.55/0.73  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.73  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.55/0.73  thf(t139_funct_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ C ) =>
% 0.55/0.73       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.55/0.73         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 0.55/0.73            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 0.55/0.73          | ~ (v1_relat_1 @ X42))),
% 0.55/0.73      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.55/0.73  thf(t175_funct_2, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73       ( ![B:$i,C:$i]:
% 0.55/0.73         ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.55/0.73           ( ( k10_relat_1 @ A @ C ) =
% 0.55/0.73             ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.55/0.73          ( ![B:$i,C:$i]:
% 0.55/0.73            ( ( r1_tarski @ ( k10_relat_1 @ A @ C ) @ B ) =>
% 0.55/0.73              ( ( k10_relat_1 @ A @ C ) =
% 0.55/0.73                ( k10_relat_1 @ ( k7_relat_1 @ A @ B ) @ C ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t175_funct_2])).
% 0.55/0.73  thf('1', plain, ((r1_tarski @ (k10_relat_1 @ sk_A @ sk_C) @ sk_B)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t103_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ C ) =>
% 0.55/0.73       ( ( r1_tarski @ A @ B ) =>
% 0.55/0.73         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.55/0.73  thf('2', plain,
% 0.55/0.73      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.55/0.73         (~ (r1_tarski @ X38 @ X39)
% 0.55/0.73          | ~ (v1_relat_1 @ X40)
% 0.55/0.73          | ((k7_relat_1 @ (k7_relat_1 @ X40 @ X39) @ X38)
% 0.55/0.73              = (k7_relat_1 @ X40 @ X38)))),
% 0.55/0.73      inference('cnf', [status(esa)], [t103_relat_1])).
% 0.55/0.73  thf('3', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf(dt_k7_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      (![X33 : $i, X34 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X33) | (v1_relat_1 @ (k7_relat_1 @ X33 @ X34)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.55/0.73  thf('5', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('6', plain,
% 0.55/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 0.55/0.73            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 0.55/0.73          | ~ (v1_relat_1 @ X42))),
% 0.55/0.73      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.55/0.73  thf(idempotence_k3_xboole_0, axiom,
% 0.55/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.55/0.73  thf('7', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.73  thf(t100_relat_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( v1_relat_1 @ C ) =>
% 0.55/0.73       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.55/0.73         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X35 @ X36) @ X37)
% 0.55/0.73            = (k7_relat_1 @ X35 @ (k3_xboole_0 @ X36 @ X37)))
% 0.55/0.73          | ~ (v1_relat_1 @ X35))),
% 0.55/0.73      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X42 @ X41) @ X43)
% 0.55/0.73            = (k3_xboole_0 @ X41 @ (k10_relat_1 @ X42 @ X43)))
% 0.55/0.73          | ~ (v1_relat_1 @ X42))),
% 0.55/0.73      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 0.55/0.73            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X3)))
% 0.55/0.73          | ~ (v1_relat_1 @ X2)
% 0.55/0.73          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.73  thf('11', plain,
% 0.55/0.73      (![X33 : $i, X34 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X33) | (v1_relat_1 @ (k7_relat_1 @ X33 @ X34)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.55/0.73  thf('12', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X2)
% 0.55/0.73          | ((k10_relat_1 @ (k7_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X3)
% 0.55/0.73              = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X3))))),
% 0.55/0.73      inference('clc', [status(thm)], ['10', '11'])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)
% 0.55/0.73            = (k3_xboole_0 @ X0 @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X0) @ X1)))
% 0.55/0.73          | ~ (v1_relat_1 @ X2))),
% 0.55/0.73      inference('sup+', [status(thm)], ['7', '12'])).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 0.55/0.73            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0))))
% 0.55/0.73          | ~ (v1_relat_1 @ X1)
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('sup+', [status(thm)], ['6', '13'])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X1)
% 0.55/0.73          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 0.55/0.73              = (k3_xboole_0 @ X2 @ 
% 0.55/0.73                 (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['14'])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X35 @ X36) @ X37)
% 0.55/0.73            = (k7_relat_1 @ X35 @ (k3_xboole_0 @ X36 @ X37)))
% 0.55/0.73          | ~ (v1_relat_1 @ X35))),
% 0.55/0.73      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ 
% 0.55/0.73               (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))
% 0.55/0.73          | ~ (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.55/0.73  thf('19', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X0)
% 0.55/0.73          | ((k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73              = (k7_relat_1 @ X0 @ 
% 0.55/0.73                 (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['18'])).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X35 @ X36) @ X37)
% 0.55/0.73            = (k7_relat_1 @ X35 @ (k3_xboole_0 @ X36 @ X37)))
% 0.55/0.73          | ~ (v1_relat_1 @ X35))),
% 0.55/0.73      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X1 @ 
% 0.55/0.73               (k3_xboole_0 @ X0 @ 
% 0.55/0.73                (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C)))))
% 0.55/0.73          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('sup+', [status(thm)], ['19', '20'])).
% 0.55/0.73  thf('22', plain,
% 0.55/0.73      (![X33 : $i, X34 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X33) | (v1_relat_1 @ (k7_relat_1 @ X33 @ X34)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.55/0.73  thf('23', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X1)
% 0.55/0.73          | ((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73              = (k7_relat_1 @ X1 @ 
% 0.55/0.73                 (k3_xboole_0 @ X0 @ 
% 0.55/0.73                  (k3_xboole_0 @ sk_B @ (k10_relat_1 @ sk_A @ sk_C))))))),
% 0.55/0.73      inference('clc', [status(thm)], ['21', '22'])).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ 
% 0.55/0.73               (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))
% 0.55/0.73          | ~ (v1_relat_1 @ sk_A)
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup+', [status(thm)], ['15', '23'])).
% 0.55/0.73  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('26', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ (k7_relat_1 @ X0 @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ 
% 0.55/0.73               (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.55/0.73  thf('27', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (((k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73            = (k7_relat_1 @ X0 @ 
% 0.55/0.73               (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))
% 0.55/0.73          | ~ (v1_relat_1 @ X0)
% 0.55/0.73          | ~ (v1_relat_1 @ X0))),
% 0.55/0.73      inference('sup+', [status(thm)], ['5', '26'])).
% 0.55/0.73  thf('28', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X0)
% 0.55/0.73          | ((k7_relat_1 @ X0 @ (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73              = (k7_relat_1 @ X0 @ 
% 0.55/0.73                 (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['27'])).
% 0.55/0.73  thf('29', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (v1_relat_1 @ X1)
% 0.55/0.73          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0)
% 0.55/0.73              = (k3_xboole_0 @ X2 @ 
% 0.55/0.73                 (k3_xboole_0 @ X2 @ (k10_relat_1 @ X1 @ X0)))))),
% 0.55/0.73      inference('simplify', [status(thm)], ['14'])).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 0.55/0.73            = (k3_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ (k10_relat_1 @ X1 @ X0)))
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('sup+', [status(thm)], ['29', '30'])).
% 0.55/0.73  thf('32', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.73  thf('33', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i]:
% 0.55/0.73         (((k10_relat_1 @ (k7_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 0.55/0.73            = (k10_relat_1 @ X1 @ X0))
% 0.55/0.73          | ~ (v1_relat_1 @ X1))),
% 0.55/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.55/0.73  thf('34', plain,
% 0.55/0.73      ((((k10_relat_1 @ 
% 0.55/0.73          (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.55/0.73           (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.55/0.73          sk_C) = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.55/0.73        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.55/0.73        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B)))),
% 0.55/0.73      inference('sup+', [status(thm)], ['28', '33'])).
% 0.55/0.73  thf('35', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_A @ sk_B))
% 0.55/0.73        | ((k10_relat_1 @ 
% 0.55/0.73            (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.55/0.73             (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.55/0.73            sk_C) = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['34'])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      ((~ (v1_relat_1 @ sk_A)
% 0.55/0.73        | ((k10_relat_1 @ 
% 0.55/0.73            (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ 
% 0.55/0.73             (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.55/0.73            sk_C) = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['4', '35'])).
% 0.55/0.73  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('38', plain,
% 0.55/0.73      (((k10_relat_1 @ 
% 0.55/0.73         (k7_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.55/0.73         sk_C) = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['36', '37'])).
% 0.55/0.73  thf('39', plain,
% 0.55/0.73      ((((k10_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ 
% 0.55/0.73          sk_C) = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.55/0.73        | ~ (v1_relat_1 @ sk_A))),
% 0.55/0.73      inference('sup+', [status(thm)], ['3', '38'])).
% 0.55/0.73  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('41', plain,
% 0.55/0.73      (((k10_relat_1 @ (k7_relat_1 @ sk_A @ (k10_relat_1 @ sk_A @ sk_C)) @ sk_C)
% 0.55/0.73         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['39', '40'])).
% 0.55/0.73  thf('42', plain,
% 0.55/0.73      ((((k3_xboole_0 @ (k10_relat_1 @ sk_A @ sk_C) @ 
% 0.55/0.73          (k10_relat_1 @ sk_A @ sk_C))
% 0.55/0.73          = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))
% 0.55/0.73        | ~ (v1_relat_1 @ sk_A))),
% 0.55/0.73      inference('sup+', [status(thm)], ['0', '41'])).
% 0.55/0.73  thf('43', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.55/0.73      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.55/0.73  thf('44', plain, ((v1_relat_1 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      (((k10_relat_1 @ sk_A @ sk_C)
% 0.55/0.73         = (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.55/0.73  thf('46', plain,
% 0.55/0.73      (((k10_relat_1 @ sk_A @ sk_C)
% 0.55/0.73         != (k10_relat_1 @ (k7_relat_1 @ sk_A @ sk_B) @ sk_C))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('47', plain, ($false),
% 0.55/0.73      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
