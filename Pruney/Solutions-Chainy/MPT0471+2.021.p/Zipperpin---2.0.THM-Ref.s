%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.30TzFPa7gT

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:49 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 183 expanded)
%              Number of leaves         :   34 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  413 ( 938 expanded)
%              Number of equality atoms :   40 ( 103 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('1',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf(t63_relat_1,conjecture,
    ( ( k3_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t63_relat_1])).

thf('2',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k3_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_relat_1 @ X1 )
       != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k3_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('6',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('7',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('9',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X19 @ X18 )
      | ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ X22 @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('13',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X12 ) @ X13 )
      | ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ ( k1_tarski @ X16 ) )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('15',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X16 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( X11 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('22',plain,(
    ! [X26: $i] :
      ( ( v1_relat_1 @ X26 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k6_subset_1 @ X5 @ ( k6_subset_1 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ X5 @ X6 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X7: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k6_subset_1 @ X20 @ X21 )
      = ( k4_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['6','9'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('39',plain,(
    ! [X29: $i] :
      ( ( ( k3_relat_1 @ X29 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X29 ) @ ( k2_relat_1 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('40',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('42',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('43',plain,
    ( ( ( k3_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ( k3_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ),
    inference(clc,[status(thm)],['17','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['13','47'])).

thf('49',plain,(
    ! [X22: $i,X23: $i] :
      ( m1_subset_1 @ X22 @ X23 ) ),
    inference(demod,[status(thm)],['12','48'])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ~ ( v1_xboole_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['11','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['10','50'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['5','51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.30TzFPa7gT
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 330 iterations in 0.209s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.66  thf(t6_boole, axiom,
% 0.45/0.66    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X11 : $i]: (((X11) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X11 : $i]: (((X11) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.66  thf(t63_relat_1, conjecture,
% 0.45/0.66    (( k3_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (( k3_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t63_relat_1])).
% 0.45/0.66  thf('2', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k3_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k3_relat_1 @ X1) != (X0))
% 0.45/0.66          | ~ (v1_xboole_0 @ X0)
% 0.45/0.66          | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '3'])).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X1 : $i]: (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k3_relat_1 @ X1)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['4'])).
% 0.45/0.66  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.45/0.66  thf('6', plain, ((v1_xboole_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.45/0.66  thf('7', plain, ((v1_xboole_0 @ sk_A)),
% 0.45/0.66      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X11 : $i]: (((X11) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.66  thf('9', plain, (((sk_A) = (k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.66  thf(d2_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.66         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.66       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.66         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]:
% 0.45/0.66         (~ (m1_subset_1 @ X19 @ X18)
% 0.45/0.66          | (v1_xboole_0 @ X19)
% 0.45/0.66          | ~ (v1_xboole_0 @ X18))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.66  thf(t1_subset, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X22 : $i, X23 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X22 @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.66  thf(l27_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k1_tarski @ X12) @ X13) | (r2_hidden @ X12 @ X13))),
% 0.45/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.66  thf(l3_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.45/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X15 : $i, X16 : $i]:
% 0.45/0.66         ((r1_tarski @ X15 @ (k1_tarski @ X16)) | ((X15) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X16))),
% 0.45/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.66  thf(t63_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.45/0.66       ( r1_xboole_0 @ A @ C ) ))).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.66         (~ (r1_tarski @ X8 @ X9)
% 0.45/0.66          | ~ (r1_xboole_0 @ X9 @ X10)
% 0.45/0.66          | (r1_xboole_0 @ X8 @ X10))),
% 0.45/0.66      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.45/0.66          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf(t60_relat_1, axiom,
% 0.45/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X11 : $i]: (((X11) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [t6_boole])).
% 0.45/0.66  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf('21', plain,
% 0.45/0.66      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['19', '20'])).
% 0.45/0.66  thf(d1_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) <=>
% 0.45/0.66       ( ![B:$i]:
% 0.45/0.66         ( ~( ( r2_hidden @ B @ A ) & 
% 0.45/0.66              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X26 : $i]: ((v1_relat_1 @ X26) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.45/0.66  thf(t48_xboole_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         ((k4_xboole_0 @ X5 @ (k4_xboole_0 @ X5 @ X6))
% 0.45/0.66           = (k3_xboole_0 @ X5 @ X6))),
% 0.45/0.66      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.66  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (![X5 : $i, X6 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X5 @ (k6_subset_1 @ X5 @ X6))
% 0.45/0.66           = (k3_xboole_0 @ X5 @ X6))),
% 0.45/0.66      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.45/0.66  thf(t4_boole, axiom,
% 0.45/0.66    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X7 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_boole])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (![X20 : $i, X21 : $i]:
% 0.45/0.66         ((k6_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X7 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['26', '29'])).
% 0.45/0.66  thf(t4_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.66            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.66       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.66            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.45/0.66          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v1_relat_1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['22', '32'])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ (k1_relat_1 @ X0) @ X1)
% 0.45/0.66          | ~ (v1_xboole_0 @ X0)
% 0.45/0.66          | (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['21', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.45/0.66          | (v1_relat_1 @ k1_xboole_0)
% 0.45/0.66          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['18', '34'])).
% 0.45/0.66  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '9'])).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['35', '36'])).
% 0.45/0.66  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf(d6_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ( k3_relat_1 @ A ) =
% 0.45/0.66         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.66  thf('39', plain,
% 0.45/0.66      (![X29 : $i]:
% 0.45/0.66         (((k3_relat_1 @ X29)
% 0.45/0.66            = (k2_xboole_0 @ (k1_relat_1 @ X29) @ (k2_relat_1 @ X29)))
% 0.45/0.66          | ~ (v1_relat_1 @ X29))),
% 0.45/0.66      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      ((((k3_relat_1 @ k1_xboole_0)
% 0.45/0.66          = (k2_xboole_0 @ k1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 0.45/0.66        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['38', '39'])).
% 0.45/0.66  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf(t1_boole, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.66  thf('42', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.66  thf('43', plain,
% 0.45/0.66      ((((k3_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.66        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.45/0.66  thf('44', plain, (((k3_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('45', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.45/0.66      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.45/0.66  thf('46', plain, (![X0 : $i]: ~ (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.66      inference('clc', [status(thm)], ['37', '45'])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1)),
% 0.45/0.66      inference('clc', [status(thm)], ['17', '46'])).
% 0.45/0.66  thf('48', plain, (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ X0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['13', '47'])).
% 0.45/0.66  thf('49', plain, (![X22 : $i, X23 : $i]: (m1_subset_1 @ X22 @ X23)),
% 0.45/0.66      inference('demod', [status(thm)], ['12', '48'])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (![X18 : $i, X19 : $i]: ((v1_xboole_0 @ X19) | ~ (v1_xboole_0 @ X18))),
% 0.45/0.66      inference('demod', [status(thm)], ['11', '49'])).
% 0.45/0.66  thf('51', plain, (![X0 : $i]: (v1_xboole_0 @ X0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '50'])).
% 0.45/0.66  thf('52', plain, (![X0 : $i]: (v1_xboole_0 @ X0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['10', '50'])).
% 0.45/0.66  thf('53', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['5', '51', '52'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
