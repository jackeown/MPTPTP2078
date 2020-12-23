%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XVOhJ9ffkN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:42 EST 2020

% Result     : Theorem 21.25s
% Output     : Refutation 21.25s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 118 expanded)
%              Number of leaves         :   17 (  40 expanded)
%              Depth                    :   23
%              Number of atoms          :  607 (1105 expanded)
%              Number of equality atoms :   68 ( 120 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X37: $i] :
      ( ( X37
       != ( k1_setfam_1 @ X32 ) )
      | ( X37 = k1_xboole_0 )
      | ( X32 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('2',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( r2_hidden @ ( sk_C_2 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_setfam_1 @ X0 ) @ ( sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ ( sk_C_2 @ k1_xboole_0 ) )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    r1_tarski @ k1_xboole_0 @ ( sk_C_2 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( sk_C_2 @ k1_xboole_0 ) )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( r2_hidden @ X30 @ X29 )
      | ~ ( r2_hidden @ X30 @ ( sk_C_2 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_2 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ X31 )
      | ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ( X31
        = ( k1_setfam_1 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( X0 = k1_xboole_0 )
      | ( X1
        = ( k1_setfam_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_3 @ X1 @ X0 ) @ ( sk_C_2 @ X0 ) )
      | ( r2_hidden @ ( sk_C_3 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C_3 @ X1 @ X0 ) @ ( sk_C_2 @ X0 ) )
      | ( X1
        = ( k1_setfam_1 @ X0 ) )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( sk_C_2 @ X0 )
        = ( k1_setfam_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_3 @ ( sk_C_2 @ X0 ) @ X0 ) @ ( sk_C_2 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['22'])).

thf('24',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ X31 )
      | ( r2_hidden @ ( sk_D_1 @ X31 @ X32 ) @ X32 )
      | ( X31
        = ( k1_setfam_1 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 )
        = ( k1_setfam_1 @ X0 ) )
      | ( k1_xboole_0 = X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( sk_C_2 @ X0 )
        = ( k1_setfam_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C_2 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C_2 @ X0 ) @ X0 ) @ X0 )
      | ( k1_xboole_0 = X0 )
      | ( ( sk_C_2 @ X0 )
        = ( k1_setfam_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('28',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ ( k1_tarski @ X0 ) )
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_D_1 @ ( sk_C_2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('31',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( r2_hidden @ ( sk_C_2 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_2 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_C_2 @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['29','35','36'])).

thf('38',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ X31 )
      | ~ ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ ( sk_D_1 @ X31 @ X32 ) )
      | ( X31
        = ( k1_setfam_1 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_3 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_3 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C_3 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ X31 )
      | ( r2_hidden @ ( sk_C_3 @ X31 @ X32 ) @ X33 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ( X31
        = ( k1_setfam_1 @ X32 ) )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_3 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C_3 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_tarski @ X0 ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['40','44'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('46',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_A != sk_A )
    | ( k1_xboole_0
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( k1_xboole_0
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X7: $i] :
      ( r2_hidden @ X7 @ ( k1_tarski @ X7 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('50',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','13'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XVOhJ9ffkN
% 0.15/0.37  % Computer   : n014.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 09:42:23 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 21.25/21.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 21.25/21.44  % Solved by: fo/fo7.sh
% 21.25/21.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 21.25/21.44  % done 8021 iterations in 20.949s
% 21.25/21.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 21.25/21.44  % SZS output start Refutation
% 21.25/21.44  thf(sk_A_type, type, sk_A: $i).
% 21.25/21.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 21.25/21.44  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 21.25/21.44  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 21.25/21.44  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 21.25/21.44  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 21.25/21.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 21.25/21.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 21.25/21.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 21.25/21.44  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 21.25/21.44  thf(d3_tarski, axiom,
% 21.25/21.44    (![A:$i,B:$i]:
% 21.25/21.44     ( ( r1_tarski @ A @ B ) <=>
% 21.25/21.44       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 21.25/21.44  thf('0', plain,
% 21.25/21.44      (![X1 : $i, X3 : $i]:
% 21.25/21.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 21.25/21.44      inference('cnf', [status(esa)], [d3_tarski])).
% 21.25/21.44  thf(d1_setfam_1, axiom,
% 21.25/21.44    (![A:$i,B:$i]:
% 21.25/21.44     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 21.25/21.44         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 21.25/21.44       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 21.25/21.44         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 21.25/21.44           ( ![C:$i]:
% 21.25/21.44             ( ( r2_hidden @ C @ B ) <=>
% 21.25/21.44               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 21.25/21.44  thf('1', plain,
% 21.25/21.44      (![X32 : $i, X37 : $i]:
% 21.25/21.44         (((X37) != (k1_setfam_1 @ X32))
% 21.25/21.44          | ((X37) = (k1_xboole_0))
% 21.25/21.44          | ((X32) != (k1_xboole_0)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 21.25/21.44  thf('2', plain, (((k1_setfam_1 @ k1_xboole_0) = (k1_xboole_0))),
% 21.25/21.44      inference('simplify', [status(thm)], ['1'])).
% 21.25/21.44  thf('3', plain,
% 21.25/21.44      (![X1 : $i, X3 : $i]:
% 21.25/21.44         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 21.25/21.44      inference('cnf', [status(esa)], [d3_tarski])).
% 21.25/21.44  thf(t7_tarski, axiom,
% 21.25/21.44    (![A:$i,B:$i]:
% 21.25/21.44     ( ~( ( r2_hidden @ A @ B ) & 
% 21.25/21.44          ( ![C:$i]:
% 21.25/21.44            ( ~( ( r2_hidden @ C @ B ) & 
% 21.25/21.44                 ( ![D:$i]:
% 21.25/21.44                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 21.25/21.44  thf('4', plain,
% 21.25/21.44      (![X28 : $i, X29 : $i]:
% 21.25/21.44         (~ (r2_hidden @ X28 @ X29) | (r2_hidden @ (sk_C_2 @ X29) @ X29))),
% 21.25/21.44      inference('cnf', [status(esa)], [t7_tarski])).
% 21.25/21.44  thf('5', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['3', '4'])).
% 21.25/21.44  thf(t4_setfam_1, axiom,
% 21.25/21.44    (![A:$i,B:$i]:
% 21.25/21.44     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 21.25/21.44  thf('6', plain,
% 21.25/21.44      (![X38 : $i, X39 : $i]:
% 21.25/21.44         ((r1_tarski @ (k1_setfam_1 @ X38) @ X39) | ~ (r2_hidden @ X39 @ X38))),
% 21.25/21.44      inference('cnf', [status(esa)], [t4_setfam_1])).
% 21.25/21.44  thf('7', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         ((r1_tarski @ X0 @ X1)
% 21.25/21.44          | (r1_tarski @ (k1_setfam_1 @ X0) @ (sk_C_2 @ X0)))),
% 21.25/21.44      inference('sup-', [status(thm)], ['5', '6'])).
% 21.25/21.44  thf('8', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         ((r1_tarski @ k1_xboole_0 @ (sk_C_2 @ k1_xboole_0))
% 21.25/21.44          | (r1_tarski @ k1_xboole_0 @ X0))),
% 21.25/21.44      inference('sup+', [status(thm)], ['2', '7'])).
% 21.25/21.44  thf('9', plain, ((r1_tarski @ k1_xboole_0 @ (sk_C_2 @ k1_xboole_0))),
% 21.25/21.44      inference('condensation', [status(thm)], ['8'])).
% 21.25/21.44  thf('10', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 21.25/21.44         (~ (r2_hidden @ X0 @ X1)
% 21.25/21.44          | (r2_hidden @ X0 @ X2)
% 21.25/21.44          | ~ (r1_tarski @ X1 @ X2))),
% 21.25/21.44      inference('cnf', [status(esa)], [d3_tarski])).
% 21.25/21.44  thf('11', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         ((r2_hidden @ X0 @ (sk_C_2 @ k1_xboole_0))
% 21.25/21.44          | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['9', '10'])).
% 21.25/21.44  thf('12', plain,
% 21.25/21.44      (![X28 : $i, X29 : $i, X30 : $i]:
% 21.25/21.44         (~ (r2_hidden @ X28 @ X29)
% 21.25/21.44          | ~ (r2_hidden @ X30 @ X29)
% 21.25/21.44          | ~ (r2_hidden @ X30 @ (sk_C_2 @ X29)))),
% 21.25/21.44      inference('cnf', [status(esa)], [t7_tarski])).
% 21.25/21.44  thf('13', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         (~ (r2_hidden @ X1 @ (sk_C_2 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 21.25/21.44      inference('condensation', [status(thm)], ['12'])).
% 21.25/21.44  thf('14', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 21.25/21.44      inference('clc', [status(thm)], ['11', '13'])).
% 21.25/21.44  thf('15', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 21.25/21.44      inference('sup-', [status(thm)], ['0', '14'])).
% 21.25/21.44  thf('16', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['3', '4'])).
% 21.25/21.44  thf(d10_xboole_0, axiom,
% 21.25/21.44    (![A:$i,B:$i]:
% 21.25/21.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 21.25/21.44  thf('17', plain,
% 21.25/21.44      (![X4 : $i, X6 : $i]:
% 21.25/21.44         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 21.25/21.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 21.25/21.44  thf('18', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         ((r2_hidden @ (sk_C_2 @ X1) @ X1)
% 21.25/21.44          | ~ (r1_tarski @ X0 @ X1)
% 21.25/21.44          | ((X0) = (X1)))),
% 21.25/21.44      inference('sup-', [status(thm)], ['16', '17'])).
% 21.25/21.44  thf('19', plain,
% 21.25/21.44      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['15', '18'])).
% 21.25/21.44  thf('20', plain,
% 21.25/21.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 21.25/21.44         ((r2_hidden @ (sk_C_3 @ X31 @ X32) @ X31)
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X31 @ X32) @ X33)
% 21.25/21.44          | ~ (r2_hidden @ X33 @ X32)
% 21.25/21.44          | ((X31) = (k1_setfam_1 @ X32))
% 21.25/21.44          | ((X32) = (k1_xboole_0)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 21.25/21.44  thf('21', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         (((k1_xboole_0) = (X0))
% 21.25/21.44          | ((X0) = (k1_xboole_0))
% 21.25/21.44          | ((X1) = (k1_setfam_1 @ X0))
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X1 @ X0) @ (sk_C_2 @ X0))
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X1 @ X0) @ X1))),
% 21.25/21.44      inference('sup-', [status(thm)], ['19', '20'])).
% 21.25/21.44  thf('22', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         ((r2_hidden @ (sk_C_3 @ X1 @ X0) @ X1)
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X1 @ X0) @ (sk_C_2 @ X0))
% 21.25/21.44          | ((X1) = (k1_setfam_1 @ X0))
% 21.25/21.44          | ((k1_xboole_0) = (X0)))),
% 21.25/21.44      inference('simplify', [status(thm)], ['21'])).
% 21.25/21.44  thf('23', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (((k1_xboole_0) = (X0))
% 21.25/21.44          | ((sk_C_2 @ X0) = (k1_setfam_1 @ X0))
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ (sk_C_2 @ X0) @ X0) @ (sk_C_2 @ X0)))),
% 21.25/21.44      inference('eq_fact', [status(thm)], ['22'])).
% 21.25/21.44  thf('24', plain,
% 21.25/21.44      (![X31 : $i, X32 : $i]:
% 21.25/21.44         (~ (r2_hidden @ (sk_C_3 @ X31 @ X32) @ X31)
% 21.25/21.44          | (r2_hidden @ (sk_D_1 @ X31 @ X32) @ X32)
% 21.25/21.44          | ((X31) = (k1_setfam_1 @ X32))
% 21.25/21.44          | ((X32) = (k1_xboole_0)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 21.25/21.44  thf('25', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (((sk_C_2 @ X0) = (k1_setfam_1 @ X0))
% 21.25/21.44          | ((k1_xboole_0) = (X0))
% 21.25/21.44          | ((X0) = (k1_xboole_0))
% 21.25/21.44          | ((sk_C_2 @ X0) = (k1_setfam_1 @ X0))
% 21.25/21.44          | (r2_hidden @ (sk_D_1 @ (sk_C_2 @ X0) @ X0) @ X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['23', '24'])).
% 21.25/21.44  thf('26', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         ((r2_hidden @ (sk_D_1 @ (sk_C_2 @ X0) @ X0) @ X0)
% 21.25/21.44          | ((k1_xboole_0) = (X0))
% 21.25/21.44          | ((sk_C_2 @ X0) = (k1_setfam_1 @ X0)))),
% 21.25/21.44      inference('simplify', [status(thm)], ['25'])).
% 21.25/21.44  thf(d1_tarski, axiom,
% 21.25/21.44    (![A:$i,B:$i]:
% 21.25/21.44     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 21.25/21.44       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 21.25/21.44  thf('27', plain,
% 21.25/21.44      (![X7 : $i, X9 : $i, X10 : $i]:
% 21.25/21.44         (~ (r2_hidden @ X10 @ X9)
% 21.25/21.44          | ((X10) = (X7))
% 21.25/21.44          | ((X9) != (k1_tarski @ X7)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_tarski])).
% 21.25/21.44  thf('28', plain,
% 21.25/21.44      (![X7 : $i, X10 : $i]:
% 21.25/21.44         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 21.25/21.44      inference('simplify', [status(thm)], ['27'])).
% 21.25/21.44  thf('29', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (((sk_C_2 @ (k1_tarski @ X0)) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | ((k1_xboole_0) = (k1_tarski @ X0))
% 21.25/21.44          | ((sk_D_1 @ (sk_C_2 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)) = (X0)))),
% 21.25/21.44      inference('sup-', [status(thm)], ['26', '28'])).
% 21.25/21.44  thf('30', plain,
% 21.25/21.44      (![X7 : $i, X8 : $i, X9 : $i]:
% 21.25/21.44         (((X8) != (X7)) | (r2_hidden @ X8 @ X9) | ((X9) != (k1_tarski @ X7)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_tarski])).
% 21.25/21.44  thf('31', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 21.25/21.44      inference('simplify', [status(thm)], ['30'])).
% 21.25/21.44  thf('32', plain,
% 21.25/21.44      (![X28 : $i, X29 : $i]:
% 21.25/21.44         (~ (r2_hidden @ X28 @ X29) | (r2_hidden @ (sk_C_2 @ X29) @ X29))),
% 21.25/21.44      inference('cnf', [status(esa)], [t7_tarski])).
% 21.25/21.44  thf('33', plain,
% 21.25/21.44      (![X0 : $i]: (r2_hidden @ (sk_C_2 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['31', '32'])).
% 21.25/21.44  thf('34', plain,
% 21.25/21.44      (![X7 : $i, X10 : $i]:
% 21.25/21.44         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 21.25/21.44      inference('simplify', [status(thm)], ['27'])).
% 21.25/21.44  thf('35', plain, (![X0 : $i]: ((sk_C_2 @ (k1_tarski @ X0)) = (X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['33', '34'])).
% 21.25/21.44  thf('36', plain, (![X0 : $i]: ((sk_C_2 @ (k1_tarski @ X0)) = (X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['33', '34'])).
% 21.25/21.44  thf('37', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | ((k1_xboole_0) = (k1_tarski @ X0))
% 21.25/21.44          | ((sk_D_1 @ X0 @ (k1_tarski @ X0)) = (X0)))),
% 21.25/21.44      inference('demod', [status(thm)], ['29', '35', '36'])).
% 21.25/21.44  thf('38', plain,
% 21.25/21.44      (![X31 : $i, X32 : $i]:
% 21.25/21.44         (~ (r2_hidden @ (sk_C_3 @ X31 @ X32) @ X31)
% 21.25/21.44          | ~ (r2_hidden @ (sk_C_3 @ X31 @ X32) @ (sk_D_1 @ X31 @ X32))
% 21.25/21.44          | ((X31) = (k1_setfam_1 @ X32))
% 21.25/21.44          | ((X32) = (k1_xboole_0)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 21.25/21.44  thf('39', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (~ (r2_hidden @ (sk_C_3 @ X0 @ (k1_tarski @ X0)) @ X0)
% 21.25/21.44          | ((k1_xboole_0) = (k1_tarski @ X0))
% 21.25/21.44          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | ((k1_tarski @ X0) = (k1_xboole_0))
% 21.25/21.44          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | ~ (r2_hidden @ (sk_C_3 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 21.25/21.44      inference('sup-', [status(thm)], ['37', '38'])).
% 21.25/21.44  thf('40', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | ((k1_xboole_0) = (k1_tarski @ X0))
% 21.25/21.44          | ~ (r2_hidden @ (sk_C_3 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 21.25/21.44      inference('simplify', [status(thm)], ['39'])).
% 21.25/21.44  thf('41', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 21.25/21.44      inference('simplify', [status(thm)], ['30'])).
% 21.25/21.44  thf('42', plain,
% 21.25/21.44      (![X31 : $i, X32 : $i, X33 : $i]:
% 21.25/21.44         ((r2_hidden @ (sk_C_3 @ X31 @ X32) @ X31)
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X31 @ X32) @ X33)
% 21.25/21.44          | ~ (r2_hidden @ X33 @ X32)
% 21.25/21.44          | ((X31) = (k1_setfam_1 @ X32))
% 21.25/21.44          | ((X32) = (k1_xboole_0)))),
% 21.25/21.44      inference('cnf', [status(esa)], [d1_setfam_1])).
% 21.25/21.44  thf('43', plain,
% 21.25/21.44      (![X0 : $i, X1 : $i]:
% 21.25/21.44         (((k1_tarski @ X0) = (k1_xboole_0))
% 21.25/21.44          | ((X1) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X1 @ (k1_tarski @ X0)) @ X0)
% 21.25/21.44          | (r2_hidden @ (sk_C_3 @ X1 @ (k1_tarski @ X0)) @ X1))),
% 21.25/21.44      inference('sup-', [status(thm)], ['41', '42'])).
% 21.25/21.44  thf('44', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         ((r2_hidden @ (sk_C_3 @ X0 @ (k1_tarski @ X0)) @ X0)
% 21.25/21.44          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 21.25/21.44          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 21.25/21.44      inference('eq_fact', [status(thm)], ['43'])).
% 21.25/21.44  thf('45', plain,
% 21.25/21.44      (![X0 : $i]:
% 21.25/21.44         (((k1_xboole_0) = (k1_tarski @ X0))
% 21.25/21.44          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 21.25/21.44      inference('clc', [status(thm)], ['40', '44'])).
% 21.25/21.44  thf(t11_setfam_1, conjecture,
% 21.25/21.44    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 21.25/21.44  thf(zf_stmt_0, negated_conjecture,
% 21.25/21.44    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 21.25/21.44    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 21.25/21.44  thf('46', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 21.25/21.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 21.25/21.44  thf('47', plain,
% 21.25/21.44      ((((sk_A) != (sk_A)) | ((k1_xboole_0) = (k1_tarski @ sk_A)))),
% 21.25/21.44      inference('sup-', [status(thm)], ['45', '46'])).
% 21.25/21.44  thf('48', plain, (((k1_xboole_0) = (k1_tarski @ sk_A))),
% 21.25/21.44      inference('simplify', [status(thm)], ['47'])).
% 21.25/21.44  thf('49', plain, (![X7 : $i]: (r2_hidden @ X7 @ (k1_tarski @ X7))),
% 21.25/21.44      inference('simplify', [status(thm)], ['30'])).
% 21.25/21.44  thf('50', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 21.25/21.44      inference('sup+', [status(thm)], ['48', '49'])).
% 21.25/21.44  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 21.25/21.44      inference('clc', [status(thm)], ['11', '13'])).
% 21.25/21.44  thf('52', plain, ($false), inference('sup-', [status(thm)], ['50', '51'])).
% 21.25/21.44  
% 21.25/21.44  % SZS output end Refutation
% 21.25/21.44  
% 21.25/21.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
