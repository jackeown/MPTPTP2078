%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XEdMYWUnFN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:24 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   71 (  89 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   15
%              Number of atoms          :  510 ( 788 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_4 ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_4 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ X21 )
      | ( r1_xboole_0 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_4 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_D @ sk_C_4 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('22',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ( X26 = X23 )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('23',plain,(
    ! [X23: $i,X26: $i] :
      ( ( X26 = X23 )
      | ~ ( r2_hidden @ X26 @ ( k1_tarski @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_C_4 ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['14','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ X0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ( r2_hidden @ ( sk_C_2 @ X13 @ X12 ) @ ( k3_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('38',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['35','41'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) ),
    inference('sup-',[status(thm)],['3','44'])).

thf('46',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('47',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_4 ) @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XEdMYWUnFN
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:22:51 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.50/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.71  % Solved by: fo/fo7.sh
% 0.50/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.71  % done 696 iterations in 0.243s
% 0.50/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.71  % SZS output start Refutation
% 0.50/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.71  thf(sk_C_4_type, type, sk_C_4: $i).
% 0.50/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.71  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.50/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.50/0.71  thf(sk_D_type, type, sk_D: $i).
% 0.50/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.50/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.50/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.50/0.71  thf(t149_zfmisc_1, conjecture,
% 0.50/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.50/0.71         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.50/0.71       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.50/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.71        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.50/0.71            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.50/0.71          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.50/0.71    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.50/0.71  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_4) @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('1', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(symmetry_r1_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('2', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.50/0.71  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_4)),
% 0.50/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.71  thf(t3_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.50/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.50/0.71            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf('4', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf('5', plain,
% 0.50/0.71      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.50/0.71  thf('6', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.50/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.50/0.71  thf('7', plain,
% 0.50/0.71      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.50/0.71      inference('demod', [status(thm)], ['5', '6'])).
% 0.50/0.71  thf(d3_tarski, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.50/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.50/0.71  thf('8', plain,
% 0.50/0.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X2 @ X3)
% 0.50/0.71          | (r2_hidden @ X2 @ X4)
% 0.50/0.71          | ~ (r1_tarski @ X3 @ X4))),
% 0.50/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.50/0.71  thf('9', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r2_hidden @ X0 @ (k1_tarski @ sk_D))
% 0.50/0.71          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.50/0.71  thf('10', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.50/0.71          | (r2_hidden @ (sk_C_1 @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)) @ 
% 0.50/0.71             (k1_tarski @ sk_D)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['4', '9'])).
% 0.50/0.71  thf('11', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf('12', plain,
% 0.50/0.71      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X10 @ X8)
% 0.50/0.71          | ~ (r2_hidden @ X10 @ X11)
% 0.50/0.71          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf('13', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X0 @ X1)
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['11', '12'])).
% 0.50/0.71  thf('14', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.50/0.71          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['10', '13'])).
% 0.50/0.71  thf('15', plain, ((r1_xboole_0 @ sk_C_4 @ sk_B)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf(t74_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.50/0.71          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.50/0.71  thf('16', plain,
% 0.50/0.71      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ X20 @ X21)
% 0.50/0.71          | (r1_xboole_0 @ X20 @ (k3_xboole_0 @ X21 @ X22)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.50/0.71  thf('17', plain,
% 0.50/0.71      (![X0 : $i]: (r1_xboole_0 @ sk_C_4 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['15', '16'])).
% 0.50/0.71  thf('18', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.50/0.71  thf('19', plain,
% 0.50/0.71      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_4)),
% 0.50/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.71  thf('20', plain, ((r2_hidden @ sk_D @ sk_C_4)),
% 0.50/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.71  thf('21', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X8))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf(d1_tarski, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.50/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.50/0.71  thf('22', plain,
% 0.50/0.71      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X26 @ X25)
% 0.50/0.71          | ((X26) = (X23))
% 0.50/0.71          | ((X25) != (k1_tarski @ X23)))),
% 0.50/0.71      inference('cnf', [status(esa)], [d1_tarski])).
% 0.50/0.71  thf('23', plain,
% 0.50/0.71      (![X23 : $i, X26 : $i]:
% 0.50/0.71         (((X26) = (X23)) | ~ (r2_hidden @ X26 @ (k1_tarski @ X23)))),
% 0.50/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.50/0.71  thf('24', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.50/0.71          | ((sk_C_1 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['21', '23'])).
% 0.50/0.71  thf('25', plain,
% 0.50/0.71      (![X8 : $i, X9 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X8 @ X9) | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ X9))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf('26', plain,
% 0.50/0.71      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X10 @ X8)
% 0.50/0.71          | ~ (r2_hidden @ X10 @ X11)
% 0.50/0.71          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf('27', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.50/0.71  thf('28', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X0 @ X1)
% 0.50/0.71          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 0.50/0.71          | ~ (r1_xboole_0 @ X2 @ X1)
% 0.50/0.71          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['24', '27'])).
% 0.50/0.71  thf('29', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ X2 @ X1)
% 0.50/0.71          | (r1_xboole_0 @ (k1_tarski @ X0) @ X2)
% 0.50/0.71          | ~ (r2_hidden @ X0 @ X1))),
% 0.50/0.71      inference('simplify', [status(thm)], ['28'])).
% 0.50/0.71  thf('30', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ X0 @ sk_C_4))),
% 0.50/0.71      inference('sup-', [status(thm)], ['20', '29'])).
% 0.50/0.71  thf('31', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['19', '30'])).
% 0.50/0.71  thf('32', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.50/0.71  thf('33', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_tarski @ sk_D))),
% 0.50/0.71      inference('sup-', [status(thm)], ['31', '32'])).
% 0.50/0.71  thf('34', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)
% 0.50/0.71          | (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0))),
% 0.50/0.71      inference('demod', [status(thm)], ['14', '33'])).
% 0.50/0.71  thf('35', plain,
% 0.50/0.71      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ X0)),
% 0.50/0.71      inference('simplify', [status(thm)], ['34'])).
% 0.50/0.71  thf(t4_xboole_0, axiom,
% 0.50/0.71    (![A:$i,B:$i]:
% 0.50/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.50/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.50/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.50/0.71  thf('36', plain,
% 0.50/0.71      (![X12 : $i, X13 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X12 @ X13)
% 0.50/0.71          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf('37', plain,
% 0.50/0.71      (![X12 : $i, X13 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X12 @ X13)
% 0.50/0.71          | (r2_hidden @ (sk_C_2 @ X13 @ X12) @ (k3_xboole_0 @ X12 @ X13)))),
% 0.50/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.50/0.71  thf('38', plain,
% 0.50/0.71      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.50/0.71         (~ (r2_hidden @ X10 @ X8)
% 0.50/0.71          | ~ (r2_hidden @ X10 @ X11)
% 0.50/0.71          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.50/0.71      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.50/0.71  thf('39', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.50/0.71          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X2))),
% 0.50/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.50/0.71  thf('40', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X1 @ X0)
% 0.50/0.71          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.71          | (r1_xboole_0 @ X1 @ X0))),
% 0.50/0.71      inference('sup-', [status(thm)], ['36', '39'])).
% 0.50/0.71  thf('41', plain,
% 0.50/0.71      (![X0 : $i, X1 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.50/0.71          | (r1_xboole_0 @ X1 @ X0))),
% 0.50/0.71      inference('simplify', [status(thm)], ['40'])).
% 0.50/0.71  thf('42', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.50/0.71      inference('sup-', [status(thm)], ['35', '41'])).
% 0.50/0.71  thf(t70_xboole_1, axiom,
% 0.50/0.71    (![A:$i,B:$i,C:$i]:
% 0.50/0.71     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.50/0.71            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.50/0.71       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.50/0.71            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.50/0.71  thf('43', plain,
% 0.50/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X16 @ (k2_xboole_0 @ X17 @ X18))
% 0.50/0.71          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.50/0.71          | ~ (r1_xboole_0 @ X16 @ X18))),
% 0.50/0.71      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.50/0.71  thf('44', plain,
% 0.50/0.71      (![X0 : $i]:
% 0.50/0.71         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.50/0.71          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.50/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.50/0.71  thf('45', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_4))),
% 0.50/0.71      inference('sup-', [status(thm)], ['3', '44'])).
% 0.50/0.71  thf('46', plain,
% 0.50/0.71      (![X6 : $i, X7 : $i]:
% 0.50/0.71         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.50/0.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.50/0.71  thf('47', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_4) @ sk_B)),
% 0.50/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.71  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.50/0.71  
% 0.50/0.71  % SZS output end Refutation
% 0.50/0.71  
% 0.50/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
