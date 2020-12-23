%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7tm4MbRt5N

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:06 EST 2020

% Result     : Theorem 0.86s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 102 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :   20
%              Number of atoms          :  605 (1139 expanded)
%              Number of equality atoms :   25 (  55 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t154_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k9_relat_1 @ B @ A )
          = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('0',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k9_relat_1 @ X36 @ X37 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X36 ) @ X37 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v2_funct_1 @ X38 )
      | ( ( k10_relat_1 @ X38 @ X39 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X38 ) @ X39 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X28: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X28: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t164_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
            & ( v2_funct_1 @ B ) )
         => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t164_funct_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X28: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k9_relat_1 @ X36 @ X37 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X36 ) @ X37 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X20 @ X21 ) @ ( k1_relat_1 @ X20 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X28: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X28 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('12',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k9_relat_1 @ X36 @ X37 )
        = ( k10_relat_1 @ ( k2_funct_1 @ X36 ) @ X37 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t154_funct_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( ( ( k10_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t157_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( r1_tarski @ X40 @ X41 )
      | ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v2_funct_1 @ X42 )
      | ~ ( r1_tarski @ X40 @ ( k1_relat_1 @ X42 ) )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X42 @ X40 ) @ ( k9_relat_1 @ X42 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t157_funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k9_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['4','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf(t147_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('27',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X34 @ ( k2_relat_1 @ X35 ) )
      | ( ( k9_relat_1 @ X35 @ ( k10_relat_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t147_funct_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['2','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_B ) @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k10_relat_1 @ sk_B @ ( k10_relat_1 @ ( k2_funct_1 @ sk_B ) @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['42','43','44','45'])).

thf('47',plain,(
    ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7tm4MbRt5N
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:03:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.86/1.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.86/1.07  % Solved by: fo/fo7.sh
% 0.86/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.86/1.07  % done 786 iterations in 0.618s
% 0.86/1.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.86/1.07  % SZS output start Refutation
% 0.86/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.86/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.86/1.07  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.86/1.07  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.86/1.07  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.86/1.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.86/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.86/1.07  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.86/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.86/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.86/1.07  thf(sk_B_type, type, sk_B: $i).
% 0.86/1.07  thf(t154_funct_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.86/1.07       ( ( v2_funct_1 @ B ) =>
% 0.86/1.07         ( ( k9_relat_1 @ B @ A ) = ( k10_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.86/1.07  thf('0', plain,
% 0.86/1.07      (![X36 : $i, X37 : $i]:
% 0.86/1.07         (~ (v2_funct_1 @ X36)
% 0.86/1.07          | ((k9_relat_1 @ X36 @ X37)
% 0.86/1.07              = (k10_relat_1 @ (k2_funct_1 @ X36) @ X37))
% 0.86/1.07          | ~ (v1_funct_1 @ X36)
% 0.86/1.07          | ~ (v1_relat_1 @ X36))),
% 0.86/1.07      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.86/1.07  thf(t155_funct_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.86/1.07       ( ( v2_funct_1 @ B ) =>
% 0.86/1.07         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.86/1.07  thf('1', plain,
% 0.86/1.07      (![X38 : $i, X39 : $i]:
% 0.86/1.07         (~ (v2_funct_1 @ X38)
% 0.86/1.07          | ((k10_relat_1 @ X38 @ X39)
% 0.86/1.07              = (k9_relat_1 @ (k2_funct_1 @ X38) @ X39))
% 0.86/1.07          | ~ (v1_funct_1 @ X38)
% 0.86/1.07          | ~ (v1_relat_1 @ X38))),
% 0.86/1.07      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.86/1.07  thf(dt_k2_funct_1, axiom,
% 0.86/1.07    (![A:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.86/1.07       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.86/1.07         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.86/1.07  thf('2', plain,
% 0.86/1.07      (![X28 : $i]:
% 0.86/1.07         ((v1_funct_1 @ (k2_funct_1 @ X28))
% 0.86/1.07          | ~ (v1_funct_1 @ X28)
% 0.86/1.07          | ~ (v1_relat_1 @ X28))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.86/1.07  thf('3', plain,
% 0.86/1.07      (![X28 : $i]:
% 0.86/1.07         ((v1_relat_1 @ (k2_funct_1 @ X28))
% 0.86/1.07          | ~ (v1_funct_1 @ X28)
% 0.86/1.07          | ~ (v1_relat_1 @ X28))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.86/1.07  thf(t164_funct_1, conjecture,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.86/1.07       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.86/1.07         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.86/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.07    (~( ![A:$i,B:$i]:
% 0.86/1.07        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.86/1.07          ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.86/1.07            ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ) )),
% 0.86/1.07    inference('cnf.neg', [status(esa)], [t164_funct_1])).
% 0.86/1.07  thf('4', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('5', plain,
% 0.86/1.07      (![X28 : $i]:
% 0.86/1.07         ((v1_relat_1 @ (k2_funct_1 @ X28))
% 0.86/1.07          | ~ (v1_funct_1 @ X28)
% 0.86/1.07          | ~ (v1_relat_1 @ X28))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.86/1.07  thf('6', plain,
% 0.86/1.07      (![X36 : $i, X37 : $i]:
% 0.86/1.07         (~ (v2_funct_1 @ X36)
% 0.86/1.07          | ((k9_relat_1 @ X36 @ X37)
% 0.86/1.07              = (k10_relat_1 @ (k2_funct_1 @ X36) @ X37))
% 0.86/1.07          | ~ (v1_funct_1 @ X36)
% 0.86/1.07          | ~ (v1_relat_1 @ X36))),
% 0.86/1.07      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.86/1.07  thf(t167_relat_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ B ) =>
% 0.86/1.07       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.86/1.07  thf('7', plain,
% 0.86/1.07      (![X20 : $i, X21 : $i]:
% 0.86/1.07         ((r1_tarski @ (k10_relat_1 @ X20 @ X21) @ (k1_relat_1 @ X20))
% 0.86/1.07          | ~ (v1_relat_1 @ X20))),
% 0.86/1.07      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.86/1.07  thf('8', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ 
% 0.86/1.07           (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.86/1.07          | ~ (v1_relat_1 @ X1)
% 0.86/1.07          | ~ (v1_funct_1 @ X1)
% 0.86/1.07          | ~ (v2_funct_1 @ X1)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X1)))),
% 0.86/1.07      inference('sup+', [status(thm)], ['6', '7'])).
% 0.86/1.07  thf('9', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 0.86/1.07             (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.86/1.07      inference('sup-', [status(thm)], ['5', '8'])).
% 0.86/1.07  thf('10', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         ((r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 0.86/1.07           (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('simplify', [status(thm)], ['9'])).
% 0.86/1.07  thf('11', plain,
% 0.86/1.07      (![X28 : $i]:
% 0.86/1.07         ((v1_relat_1 @ (k2_funct_1 @ X28))
% 0.86/1.07          | ~ (v1_funct_1 @ X28)
% 0.86/1.07          | ~ (v1_relat_1 @ X28))),
% 0.86/1.07      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.86/1.07  thf('12', plain,
% 0.86/1.07      (![X36 : $i, X37 : $i]:
% 0.86/1.07         (~ (v2_funct_1 @ X36)
% 0.86/1.07          | ((k9_relat_1 @ X36 @ X37)
% 0.86/1.07              = (k10_relat_1 @ (k2_funct_1 @ X36) @ X37))
% 0.86/1.07          | ~ (v1_funct_1 @ X36)
% 0.86/1.07          | ~ (v1_relat_1 @ X36))),
% 0.86/1.07      inference('cnf', [status(esa)], [t154_funct_1])).
% 0.86/1.07  thf(t169_relat_1, axiom,
% 0.86/1.07    (![A:$i]:
% 0.86/1.07     ( ( v1_relat_1 @ A ) =>
% 0.86/1.07       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.86/1.07  thf('13', plain,
% 0.86/1.07      (![X22 : $i]:
% 0.86/1.07         (((k10_relat_1 @ X22 @ (k2_relat_1 @ X22)) = (k1_relat_1 @ X22))
% 0.86/1.07          | ~ (v1_relat_1 @ X22))),
% 0.86/1.07      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.86/1.07  thf('14', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.86/1.07      inference('sup+', [status(thm)], ['12', '13'])).
% 0.86/1.07  thf('15', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07              = (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.86/1.07      inference('sup-', [status(thm)], ['11', '14'])).
% 0.86/1.07  thf('16', plain,
% 0.86/1.07      (![X0 : $i]:
% 0.86/1.07         (((k9_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07            = (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('simplify', [status(thm)], ['15'])).
% 0.86/1.07  thf(t157_funct_1, axiom,
% 0.86/1.07    (![A:$i,B:$i,C:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.86/1.07       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.86/1.07           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.86/1.07         ( r1_tarski @ A @ B ) ) ))).
% 0.86/1.07  thf('17', plain,
% 0.86/1.07      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.86/1.07         ((r1_tarski @ X40 @ X41)
% 0.86/1.07          | ~ (v1_relat_1 @ X42)
% 0.86/1.07          | ~ (v1_funct_1 @ X42)
% 0.86/1.07          | ~ (v2_funct_1 @ X42)
% 0.86/1.07          | ~ (r1_tarski @ X40 @ (k1_relat_1 @ X42))
% 0.86/1.07          | ~ (r1_tarski @ (k9_relat_1 @ X42 @ X40) @ (k9_relat_1 @ X42 @ X41)))),
% 0.86/1.07      inference('cnf', [status(esa)], [t157_funct_1])).
% 0.86/1.07  thf('18', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         (~ (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 0.86/1.07             (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | (r1_tarski @ X1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.86/1.07      inference('sup-', [status(thm)], ['16', '17'])).
% 0.86/1.07  thf('19', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         ((r1_tarski @ X1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07          | ~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (r1_tarski @ (k9_relat_1 @ X0 @ X1) @ 
% 0.86/1.07               (k1_relat_1 @ (k2_funct_1 @ X0))))),
% 0.86/1.07      inference('simplify', [status(thm)], ['18'])).
% 0.86/1.07  thf('20', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         (~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.86/1.07          | (r1_tarski @ X1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.86/1.07      inference('sup-', [status(thm)], ['10', '19'])).
% 0.86/1.07  thf('21', plain,
% 0.86/1.07      (![X0 : $i, X1 : $i]:
% 0.86/1.07         ((r1_tarski @ X1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.86/1.07          | ~ (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.86/1.07          | ~ (v2_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_funct_1 @ X0)
% 0.86/1.07          | ~ (v1_relat_1 @ X0))),
% 0.86/1.07      inference('simplify', [status(thm)], ['20'])).
% 0.86/1.07  thf('22', plain,
% 0.86/1.07      ((~ (v1_relat_1 @ sk_B)
% 0.86/1.07        | ~ (v1_funct_1 @ sk_B)
% 0.86/1.07        | ~ (v2_funct_1 @ sk_B)
% 0.86/1.07        | (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B))))),
% 0.86/1.07      inference('sup-', [status(thm)], ['4', '21'])).
% 0.86/1.07  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('25', plain, ((v2_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('26', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_B)))),
% 0.86/1.07      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.86/1.07  thf(t147_funct_1, axiom,
% 0.86/1.07    (![A:$i,B:$i]:
% 0.86/1.07     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.86/1.07       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.86/1.07         ( ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.86/1.07  thf('27', plain,
% 0.86/1.07      (![X34 : $i, X35 : $i]:
% 0.86/1.07         (~ (r1_tarski @ X34 @ (k2_relat_1 @ X35))
% 0.86/1.07          | ((k9_relat_1 @ X35 @ (k10_relat_1 @ X35 @ X34)) = (X34))
% 0.86/1.07          | ~ (v1_funct_1 @ X35)
% 0.86/1.07          | ~ (v1_relat_1 @ X35))),
% 0.86/1.07      inference('cnf', [status(esa)], [t147_funct_1])).
% 0.86/1.07  thf('28', plain,
% 0.86/1.07      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_B))
% 0.86/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 0.86/1.07        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.86/1.07            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['26', '27'])).
% 0.86/1.07  thf('29', plain,
% 0.86/1.07      ((~ (v1_relat_1 @ sk_B)
% 0.86/1.07        | ~ (v1_funct_1 @ sk_B)
% 0.86/1.07        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.86/1.07            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))
% 0.86/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['3', '28'])).
% 0.86/1.07  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('31', plain, ((v1_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('32', plain,
% 0.86/1.07      ((((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.86/1.07          (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))
% 0.86/1.07        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 0.86/1.07      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.86/1.07  thf('33', plain,
% 0.86/1.07      ((~ (v1_relat_1 @ sk_B)
% 0.86/1.07        | ~ (v1_funct_1 @ sk_B)
% 0.86/1.07        | ((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.86/1.07            (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A)))),
% 0.86/1.07      inference('sup-', [status(thm)], ['2', '32'])).
% 0.86/1.07  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('35', plain, ((v1_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('36', plain,
% 0.86/1.07      (((k9_relat_1 @ (k2_funct_1 @ sk_B) @ 
% 0.86/1.07         (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A)) = (sk_A))),
% 0.86/1.07      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.86/1.07  thf('37', plain,
% 0.86/1.07      ((((k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 0.86/1.07          = (sk_A))
% 0.86/1.07        | ~ (v1_relat_1 @ sk_B)
% 0.86/1.07        | ~ (v1_funct_1 @ sk_B)
% 0.86/1.07        | ~ (v2_funct_1 @ sk_B))),
% 0.86/1.07      inference('sup+', [status(thm)], ['1', '36'])).
% 0.86/1.07  thf('38', plain, ((v1_relat_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('39', plain, ((v1_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('40', plain, ((v2_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('41', plain,
% 0.86/1.07      (((k10_relat_1 @ sk_B @ (k10_relat_1 @ (k2_funct_1 @ sk_B) @ sk_A))
% 0.86/1.07         = (sk_A))),
% 0.86/1.07      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.86/1.07  thf('42', plain,
% 0.86/1.07      ((((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))
% 0.86/1.07        | ~ (v1_relat_1 @ sk_B)
% 0.86/1.07        | ~ (v1_funct_1 @ sk_B)
% 0.86/1.07        | ~ (v2_funct_1 @ sk_B))),
% 0.86/1.07      inference('sup+', [status(thm)], ['0', '41'])).
% 0.86/1.07  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('44', plain, ((v1_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('45', plain, ((v2_funct_1 @ sk_B)),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('46', plain,
% 0.86/1.07      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.86/1.07      inference('demod', [status(thm)], ['42', '43', '44', '45'])).
% 0.86/1.07  thf('47', plain,
% 0.86/1.07      (((k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) != (sk_A))),
% 0.86/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.07  thf('48', plain, ($false),
% 0.86/1.07      inference('simplify_reflect-', [status(thm)], ['46', '47'])).
% 0.86/1.07  
% 0.86/1.07  % SZS output end Refutation
% 0.86/1.07  
% 0.91/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
