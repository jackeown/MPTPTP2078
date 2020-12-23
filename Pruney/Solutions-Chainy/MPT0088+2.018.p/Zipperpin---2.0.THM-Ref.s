%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hl6kJpfxyj

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:37 EST 2020

% Result     : Theorem 3.80s
% Output     : Refutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   61 (  86 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  585 ( 952 expanded)
%              Number of equality atoms :   18 (  30 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t81_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
       => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('4',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('25',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( X1
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X3 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X1 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['29','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hl6kJpfxyj
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:35:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.80/4.05  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.80/4.05  % Solved by: fo/fo7.sh
% 3.80/4.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.80/4.05  % done 4845 iterations in 3.596s
% 3.80/4.05  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.80/4.05  % SZS output start Refutation
% 3.80/4.05  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.80/4.05  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.80/4.05  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.80/4.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.80/4.05  thf(sk_B_type, type, sk_B: $i).
% 3.80/4.05  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.80/4.05  thf(sk_A_type, type, sk_A: $i).
% 3.80/4.05  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.80/4.05  thf(t81_xboole_1, conjecture,
% 3.80/4.05    (![A:$i,B:$i,C:$i]:
% 3.80/4.05     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 3.80/4.05       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 3.80/4.05  thf(zf_stmt_0, negated_conjecture,
% 3.80/4.05    (~( ![A:$i,B:$i,C:$i]:
% 3.80/4.05        ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 3.80/4.05          ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )),
% 3.80/4.05    inference('cnf.neg', [status(esa)], [t81_xboole_1])).
% 3.80/4.05  thf('0', plain, (~ (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.80/4.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.05  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 3.80/4.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.80/4.05  thf(t3_xboole_0, axiom,
% 3.80/4.05    (![A:$i,B:$i]:
% 3.80/4.05     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.80/4.05            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.80/4.05       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.80/4.05            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.80/4.05  thf('2', plain,
% 3.80/4.05      (![X6 : $i, X7 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('3', plain,
% 3.80/4.05      (![X6 : $i, X7 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('4', plain,
% 3.80/4.05      (![X6 : $i, X8 : $i, X9 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X8 @ X6)
% 3.80/4.05          | ~ (r2_hidden @ X8 @ X9)
% 3.80/4.05          | ~ (r1_xboole_0 @ X6 @ X9))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('5', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X1 @ X0)
% 3.80/4.05          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.80/4.05          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 3.80/4.05      inference('sup-', [status(thm)], ['3', '4'])).
% 3.80/4.05  thf('6', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X0 @ X1)
% 3.80/4.05          | ~ (r1_xboole_0 @ X1 @ X0)
% 3.80/4.05          | (r1_xboole_0 @ X0 @ X1))),
% 3.80/4.05      inference('sup-', [status(thm)], ['2', '5'])).
% 3.80/4.05  thf('7', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 3.80/4.05      inference('simplify', [status(thm)], ['6'])).
% 3.80/4.05  thf('8', plain, ((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 3.80/4.05      inference('sup-', [status(thm)], ['1', '7'])).
% 3.80/4.05  thf('9', plain,
% 3.80/4.05      (![X6 : $i, X7 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf(d5_xboole_0, axiom,
% 3.80/4.05    (![A:$i,B:$i,C:$i]:
% 3.80/4.05     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 3.80/4.05       ( ![D:$i]:
% 3.80/4.05         ( ( r2_hidden @ D @ C ) <=>
% 3.80/4.05           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 3.80/4.05  thf('10', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X4 @ X3)
% 3.80/4.05          | (r2_hidden @ X4 @ X1)
% 3.80/4.05          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.80/4.05  thf('11', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.80/4.05         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['10'])).
% 3.80/4.05  thf('12', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 3.80/4.05          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 3.80/4.05      inference('sup-', [status(thm)], ['9', '11'])).
% 3.80/4.05  thf('13', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X1 @ X0)
% 3.80/4.05          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.80/4.05          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 3.80/4.05      inference('sup-', [status(thm)], ['3', '4'])).
% 3.80/4.05  thf('14', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2)
% 3.80/4.05          | ~ (r1_xboole_0 @ X2 @ X0)
% 3.80/4.05          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 3.80/4.05      inference('sup-', [status(thm)], ['12', '13'])).
% 3.80/4.05  thf('15', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         (~ (r1_xboole_0 @ X2 @ X0)
% 3.80/4.05          | (r1_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X2))),
% 3.80/4.05      inference('simplify', [status(thm)], ['14'])).
% 3.80/4.05  thf('16', plain,
% 3.80/4.05      (![X0 : $i]:
% 3.80/4.05         (r1_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 3.80/4.05          (k4_xboole_0 @ sk_B @ sk_C_1))),
% 3.80/4.05      inference('sup-', [status(thm)], ['8', '15'])).
% 3.80/4.05  thf('17', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.80/4.05         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 3.80/4.05          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.80/4.05          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.80/4.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.80/4.05  thf('18', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.80/4.05          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.80/4.05      inference('eq_fact', [status(thm)], ['17'])).
% 3.80/4.05  thf('19', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X5 : $i]:
% 3.80/4.05         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 3.80/4.05          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 3.80/4.05          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 3.80/4.05          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 3.80/4.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.80/4.05  thf('20', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.80/4.05          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.80/4.05          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.80/4.05          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.80/4.05      inference('sup-', [status(thm)], ['18', '19'])).
% 3.80/4.05  thf('21', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 3.80/4.05          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.80/4.05          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['20'])).
% 3.80/4.05  thf('22', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.80/4.05          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.80/4.05      inference('eq_fact', [status(thm)], ['17'])).
% 3.80/4.05  thf('23', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.80/4.05          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 3.80/4.05      inference('clc', [status(thm)], ['21', '22'])).
% 3.80/4.05  thf('24', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 3.80/4.05          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 3.80/4.05      inference('eq_fact', [status(thm)], ['17'])).
% 3.80/4.05  thf('25', plain,
% 3.80/4.05      (![X6 : $i, X8 : $i, X9 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X8 @ X6)
% 3.80/4.05          | ~ (r2_hidden @ X8 @ X9)
% 3.80/4.05          | ~ (r1_xboole_0 @ X6 @ X9))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('26', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 3.80/4.05          | ~ (r1_xboole_0 @ X0 @ X2)
% 3.80/4.05          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X2))),
% 3.80/4.05      inference('sup-', [status(thm)], ['24', '25'])).
% 3.80/4.05  thf('27', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         (((X1) = (k4_xboole_0 @ X1 @ X0))
% 3.80/4.05          | ~ (r1_xboole_0 @ X1 @ X0)
% 3.80/4.05          | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 3.80/4.05      inference('sup-', [status(thm)], ['23', '26'])).
% 3.80/4.05  thf('28', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i]:
% 3.80/4.05         (~ (r1_xboole_0 @ X1 @ X0) | ((X1) = (k4_xboole_0 @ X1 @ X0)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['27'])).
% 3.80/4.05  thf('29', plain,
% 3.80/4.05      (![X0 : $i]:
% 3.80/4.05         ((k4_xboole_0 @ sk_A @ X0)
% 3.80/4.05           = (k4_xboole_0 @ (k4_xboole_0 @ sk_A @ X0) @ 
% 3.80/4.05              (k4_xboole_0 @ sk_B @ sk_C_1)))),
% 3.80/4.05      inference('sup-', [status(thm)], ['16', '28'])).
% 3.80/4.05  thf('30', plain,
% 3.80/4.05      (![X6 : $i, X7 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('31', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X0 @ X1)
% 3.80/4.05          | (r2_hidden @ X0 @ X2)
% 3.80/4.05          | (r2_hidden @ X0 @ X3)
% 3.80/4.05          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.80/4.05  thf('32', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 3.80/4.05          | (r2_hidden @ X0 @ X2)
% 3.80/4.05          | ~ (r2_hidden @ X0 @ X1))),
% 3.80/4.05      inference('simplify', [status(thm)], ['31'])).
% 3.80/4.05  thf('33', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X0 @ X1)
% 3.80/4.05          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 3.80/4.05          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 3.80/4.05      inference('sup-', [status(thm)], ['30', '32'])).
% 3.80/4.05  thf('34', plain,
% 3.80/4.05      (![X6 : $i, X7 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('35', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X4 @ X3)
% 3.80/4.05          | ~ (r2_hidden @ X4 @ X2)
% 3.80/4.05          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('cnf', [status(esa)], [d5_xboole_0])).
% 3.80/4.05  thf('36', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X4 @ X2)
% 3.80/4.05          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['35'])).
% 3.80/4.05  thf('37', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.80/4.05          | ~ (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 3.80/4.05      inference('sup-', [status(thm)], ['34', '36'])).
% 3.80/4.05  thf('38', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r2_hidden @ 
% 3.80/4.05           (sk_C @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1) @ X0)
% 3.80/4.05          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 3.80/4.05          | (r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.80/4.05      inference('sup-', [status(thm)], ['33', '37'])).
% 3.80/4.05  thf('39', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X1 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 3.80/4.05          | (r2_hidden @ 
% 3.80/4.05             (sk_C @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1) @ X0))),
% 3.80/4.05      inference('simplify', [status(thm)], ['38'])).
% 3.80/4.05  thf('40', plain,
% 3.80/4.05      (![X6 : $i, X7 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 3.80/4.05      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.80/4.05  thf('41', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.80/4.05         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['10'])).
% 3.80/4.05  thf('42', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.80/4.05          | (r2_hidden @ (sk_C @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X1))),
% 3.80/4.05      inference('sup-', [status(thm)], ['40', '41'])).
% 3.80/4.05  thf('43', plain,
% 3.80/4.05      (![X1 : $i, X2 : $i, X4 : $i]:
% 3.80/4.05         (~ (r2_hidden @ X4 @ X2)
% 3.80/4.05          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['35'])).
% 3.80/4.05  thf('44', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X2 @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X3))
% 3.80/4.05          | ~ (r2_hidden @ 
% 3.80/4.05               (sk_C @ (k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X3) @ X2) @ X0))),
% 3.80/4.05      inference('sup-', [status(thm)], ['42', '43'])).
% 3.80/4.05  thf('45', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         ((r1_xboole_0 @ X1 @ 
% 3.80/4.05           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))
% 3.80/4.05          | (r1_xboole_0 @ X1 @ 
% 3.80/4.05             (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0))))),
% 3.80/4.05      inference('sup-', [status(thm)], ['39', '44'])).
% 3.80/4.05  thf('46', plain,
% 3.80/4.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.80/4.05         (r1_xboole_0 @ X1 @ 
% 3.80/4.05          (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 3.80/4.05      inference('simplify', [status(thm)], ['45'])).
% 3.80/4.05  thf('47', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1))),
% 3.80/4.05      inference('sup+', [status(thm)], ['29', '46'])).
% 3.80/4.05  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 3.80/4.05  
% 3.80/4.05  % SZS output end Refutation
% 3.80/4.05  
% 3.80/4.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
