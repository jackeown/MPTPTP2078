%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G0lrpm2Q0v

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:18 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 110 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :   15
%              Number of atoms          :  468 ( 643 expanded)
%              Number of equality atoms :   57 (  79 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X3 )
      = X3 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('7',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X49 @ X48 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X49 ) @ ( k4_relat_1 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k6_subset_1 @ X35 @ X36 )
      = ( k4_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( v1_relat_1 @ X48 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X49 @ X48 ) )
        = ( k4_xboole_0 @ ( k4_relat_1 @ X49 ) @ ( k4_relat_1 @ X48 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('14',plain,(
    ! [X42: $i,X45: $i] :
      ( ( X45
        = ( k1_relat_1 @ X42 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X45 @ X42 ) @ ( sk_D @ X45 @ X42 ) ) @ X42 )
      | ( r2_hidden @ ( sk_C @ X45 @ X42 ) @ X45 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X47: $i] :
      ( ( ( k1_relat_1 @ X47 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X47 ) ) )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('23',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_relat_1 @ X1 )
         != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['23'])).

thf('41',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['31','41'])).

thf('43',plain,(
    ! [X39: $i] :
      ( ( v1_relat_1 @ X39 )
      | ~ ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(demod,[status(thm)],['45','46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','52'])).

thf('54',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G0lrpm2Q0v
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.37/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.55  % Solved by: fo/fo7.sh
% 0.37/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.55  % done 237 iterations in 0.088s
% 0.37/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.55  % SZS output start Refutation
% 0.37/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.37/0.55  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.37/0.55  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.37/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.37/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.55  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf(cc1_relat_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.37/0.55  thf('1', plain, (![X39 : $i]: ((v1_relat_1 @ X39) | ~ (v1_xboole_0 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.55  thf(t92_xboole_1, axiom,
% 0.37/0.55    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf('2', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf(idempotence_k3_xboole_0, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.37/0.55  thf('3', plain, (![X3 : $i]: ((k3_xboole_0 @ X3 @ X3) = (X3))),
% 0.37/0.55      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.37/0.55  thf(t100_xboole_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.55  thf('4', plain,
% 0.37/0.55      (![X5 : $i, X6 : $i]:
% 0.37/0.55         ((k4_xboole_0 @ X5 @ X6)
% 0.37/0.55           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.37/0.55      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.55  thf('5', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('6', plain, (![X7 : $i]: ((k4_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.37/0.55      inference('demod', [status(thm)], ['2', '5'])).
% 0.37/0.55  thf(t41_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ![B:$i]:
% 0.37/0.55         ( ( v1_relat_1 @ B ) =>
% 0.37/0.55           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.37/0.55             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.37/0.55  thf('7', plain,
% 0.37/0.55      (![X48 : $i, X49 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X48)
% 0.37/0.55          | ((k4_relat_1 @ (k6_subset_1 @ X49 @ X48))
% 0.37/0.55              = (k6_subset_1 @ (k4_relat_1 @ X49) @ (k4_relat_1 @ X48)))
% 0.37/0.55          | ~ (v1_relat_1 @ X49))),
% 0.37/0.55      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.37/0.55  thf(redefinition_k6_subset_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.37/0.55  thf('8', plain,
% 0.37/0.55      (![X35 : $i, X36 : $i]:
% 0.37/0.55         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.55  thf('9', plain,
% 0.37/0.55      (![X35 : $i, X36 : $i]:
% 0.37/0.55         ((k6_subset_1 @ X35 @ X36) = (k4_xboole_0 @ X35 @ X36))),
% 0.37/0.55      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.37/0.55  thf('10', plain,
% 0.37/0.55      (![X48 : $i, X49 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X48)
% 0.37/0.55          | ((k4_relat_1 @ (k4_xboole_0 @ X49 @ X48))
% 0.37/0.55              = (k4_xboole_0 @ (k4_relat_1 @ X49) @ (k4_relat_1 @ X48)))
% 0.37/0.55          | ~ (v1_relat_1 @ X49))),
% 0.37/0.55      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.37/0.55  thf('11', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['6', '10'])).
% 0.37/0.55  thf('12', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_relat_1 @ X0)
% 0.37/0.55          | ((k4_relat_1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.55  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf(d4_relat_1, axiom,
% 0.37/0.55    (![A:$i,B:$i]:
% 0.37/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.37/0.55       ( ![C:$i]:
% 0.37/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.37/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.37/0.55  thf('14', plain,
% 0.37/0.55      (![X42 : $i, X45 : $i]:
% 0.37/0.55         (((X45) = (k1_relat_1 @ X42))
% 0.37/0.55          | (r2_hidden @ 
% 0.37/0.55             (k4_tarski @ (sk_C @ X45 @ X42) @ (sk_D @ X45 @ X42)) @ X42)
% 0.37/0.55          | (r2_hidden @ (sk_C @ X45 @ X42) @ X45))),
% 0.37/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.37/0.55  thf(d1_xboole_0, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.55  thf('15', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.55  thf('16', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.37/0.55          | ((X1) = (k1_relat_1 @ X0))
% 0.37/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.55  thf('17', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.55  thf('18', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ X1)
% 0.37/0.55          | ((X0) = (k1_relat_1 @ X1))
% 0.37/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('19', plain,
% 0.37/0.55      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['13', '18'])).
% 0.37/0.55  thf(t37_relat_1, axiom,
% 0.37/0.55    (![A:$i]:
% 0.37/0.55     ( ( v1_relat_1 @ A ) =>
% 0.37/0.55       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.37/0.55         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.37/0.55  thf('20', plain,
% 0.37/0.55      (![X47 : $i]:
% 0.37/0.55         (((k1_relat_1 @ X47) = (k2_relat_1 @ (k4_relat_1 @ X47)))
% 0.37/0.55          | ~ (v1_relat_1 @ X47))),
% 0.37/0.55      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.37/0.55  thf(l13_xboole_0, axiom,
% 0.37/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.55  thf('21', plain,
% 0.37/0.55      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.55  thf('22', plain,
% 0.37/0.55      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.37/0.55      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.55  thf(t60_relat_1, conjecture,
% 0.37/0.55    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.55     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.55    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.55        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.37/0.55    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.37/0.55  thf('23', plain,
% 0.37/0.55      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.37/0.55        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.55  thf('24', plain,
% 0.37/0.55      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('split', [status(esa)], ['23'])).
% 0.37/0.55  thf('25', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['22', '24'])).
% 0.37/0.55  thf('26', plain,
% 0.37/0.55      ((![X0 : $i, X1 : $i]:
% 0.37/0.55          (((k2_relat_1 @ X1) != (X0))
% 0.37/0.55           | ~ (v1_xboole_0 @ X0)
% 0.37/0.55           | ~ (v1_xboole_0 @ X1)))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['21', '25'])).
% 0.37/0.55  thf('27', plain,
% 0.37/0.55      ((![X1 : $i]:
% 0.37/0.55          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1))))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.37/0.55  thf('28', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.37/0.55           | ~ (v1_relat_1 @ X0)
% 0.37/0.55           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['20', '27'])).
% 0.37/0.55  thf('29', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55           | ~ (v1_xboole_0 @ X0)
% 0.37/0.55           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.37/0.55           | ~ (v1_relat_1 @ X0)))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['19', '28'])).
% 0.37/0.55  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('31', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (~ (v1_xboole_0 @ X0)
% 0.37/0.55           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.37/0.55           | ~ (v1_relat_1 @ X0)))
% 0.37/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.55  thf('32', plain,
% 0.37/0.55      (![X0 : $i, X1 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ X1)
% 0.37/0.55          | ((X0) = (k1_relat_1 @ X1))
% 0.37/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.55  thf('33', plain,
% 0.37/0.55      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('split', [status(esa)], ['23'])).
% 0.37/0.55  thf('34', plain,
% 0.37/0.55      ((![X0 : $i]:
% 0.37/0.55          (((X0) != (k1_xboole_0))
% 0.37/0.55           | ~ (v1_xboole_0 @ X0)
% 0.37/0.55           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.55  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('36', plain,
% 0.37/0.55      ((![X0 : $i]: (((X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.37/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('demod', [status(thm)], ['34', '35'])).
% 0.37/0.55  thf('37', plain,
% 0.37/0.55      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.37/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.55      inference('simplify', [status(thm)], ['36'])).
% 0.37/0.55  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('39', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.55      inference('simplify_reflect+', [status(thm)], ['37', '38'])).
% 0.37/0.55  thf('40', plain,
% 0.37/0.55      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.37/0.55       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.55      inference('split', [status(esa)], ['23'])).
% 0.37/0.55  thf('41', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.55      inference('sat_resolution*', [status(thm)], ['39', '40'])).
% 0.37/0.55  thf('42', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ X0)
% 0.37/0.55          | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.37/0.55          | ~ (v1_relat_1 @ X0))),
% 0.37/0.55      inference('simpl_trail', [status(thm)], ['31', '41'])).
% 0.37/0.55  thf('43', plain, (![X39 : $i]: ((v1_relat_1 @ X39) | ~ (v1_xboole_0 @ X39))),
% 0.37/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.55  thf('44', plain,
% 0.37/0.55      (![X0 : $i]: (~ (v1_xboole_0 @ (k4_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.55      inference('clc', [status(thm)], ['42', '43'])).
% 0.37/0.55  thf('45', plain,
% 0.37/0.55      (![X0 : $i]:
% 0.37/0.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.55          | ~ (v1_relat_1 @ X0)
% 0.37/0.55          | ~ (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0)))),
% 0.37/0.55      inference('sup-', [status(thm)], ['12', '44'])).
% 0.37/0.55  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('47', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.37/0.55      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.55  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.55  thf('49', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['47', '48'])).
% 0.37/0.55  thf('50', plain,
% 0.37/0.55      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('sup+', [status(thm)], ['3', '4'])).
% 0.37/0.55  thf('51', plain, (![X0 : $i]: (v1_xboole_0 @ (k4_xboole_0 @ X0 @ X0))),
% 0.37/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.37/0.55  thf('52', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.37/0.55      inference('demod', [status(thm)], ['45', '46', '51'])).
% 0.37/0.55  thf('53', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.37/0.55      inference('sup-', [status(thm)], ['1', '52'])).
% 0.37/0.55  thf('54', plain, ($false), inference('sup-', [status(thm)], ['0', '53'])).
% 0.37/0.55  
% 0.37/0.55  % SZS output end Refutation
% 0.37/0.55  
% 0.37/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
