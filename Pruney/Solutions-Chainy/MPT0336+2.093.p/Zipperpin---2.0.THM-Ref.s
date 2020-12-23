%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2c1ByPfJLI

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:32 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 116 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  547 ( 931 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k4_xboole_0 @ X33 @ ( k1_tarski @ X34 ) )
        = X33 )
      | ( r2_hidden @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_xboole_0 @ X23 @ X25 )
      | ( ( k4_xboole_0 @ X23 @ X25 )
       != X23 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
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

thf('21',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('31',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ~ ( r1_xboole_0 @ X20 @ ( k3_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_2 )
    = sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('40',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
      | ~ ( r1_xboole_0 @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','47'])).

thf('49',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['6','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('51',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('55',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2c1ByPfJLI
% 0.11/0.33  % Computer   : n016.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 09:42:19 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.34  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 513 iterations in 0.179s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.62  thf(t149_zfmisc_1, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.41/0.62         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.41/0.62       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.41/0.62            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.41/0.62          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.41/0.62  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.62  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain,
% 0.41/0.62      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(commutativity_k3_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.41/0.62      inference('demod', [status(thm)], ['4', '5'])).
% 0.41/0.62  thf(t65_zfmisc_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.41/0.62       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X33 : $i, X34 : $i]:
% 0.41/0.62         (((k4_xboole_0 @ X33 @ (k1_tarski @ X34)) = (X33))
% 0.41/0.62          | (r2_hidden @ X34 @ X33))),
% 0.41/0.62      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.41/0.62  thf(t83_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X23 : $i, X25 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X23 @ X25) | ((k4_xboole_0 @ X23 @ X25) != (X23)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (((X0) != (X0))
% 0.41/0.62          | (r2_hidden @ X1 @ X0)
% 0.41/0.62          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.41/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.62  thf(t70_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.41/0.62            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.41/0.62       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.41/0.62            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X14 @ X15)
% 0.41/0.62          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.41/0.62          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.62  thf('15', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('16', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('17', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.41/0.62          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.41/0.62          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 0.41/0.62          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.62  thf('19', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['15', '18'])).
% 0.41/0.62  thf('20', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(t3_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.41/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X6 @ X4)
% 0.41/0.62          | ~ (r2_hidden @ X6 @ X7)
% 0.41/0.62          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf('23', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['19', '22'])).
% 0.41/0.62  thf('24', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['14', '23'])).
% 0.41/0.62  thf('25', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.62  thf('26', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 0.41/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i]:
% 0.41/0.62         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.41/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.62  thf('28', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.41/0.62  thf(t48_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X12 : $i, X13 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.41/0.62           = (k3_xboole_0 @ X12 @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['28', '29'])).
% 0.41/0.62  thf(t77_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.41/0.62          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X20 @ X21)
% 0.41/0.62          | ~ (r1_xboole_0 @ X20 @ (k3_xboole_0 @ X21 @ X22))
% 0.41/0.62          | ~ (r1_tarski @ X20 @ X22))),
% 0.41/0.62      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.41/0.62  thf('32', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))
% 0.41/0.62          | ~ (r1_tarski @ X0 @ (k1_tarski @ sk_D))
% 0.41/0.62          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      (![X4 : $i, X5 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C @ X5 @ X4) @ X4))),
% 0.41/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.41/0.62  thf('34', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X23 : $i, X24 : $i]:
% 0.41/0.62         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.41/0.62      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.41/0.62  thf('36', plain, (((k4_xboole_0 @ sk_B @ sk_C_2) = (sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain,
% 0.41/0.62      (![X12 : $i, X13 : $i]:
% 0.41/0.62         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.41/0.62           = (k3_xboole_0 @ X12 @ X13))),
% 0.41/0.62      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C_2))),
% 0.41/0.62      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.62  thf(t4_xboole_0, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.41/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.41/0.62  thf('40', plain,
% 0.41/0.62      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.41/0.62          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.41/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.41/0.62  thf('41', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.62          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))
% 0.41/0.62          | ~ (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['38', '41'])).
% 0.41/0.62  thf('43', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['42', '43'])).
% 0.41/0.62  thf('45', plain,
% 0.41/0.62      (![X0 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B) @ X0)),
% 0.41/0.62      inference('sup-', [status(thm)], ['33', '44'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.62  thf('47', plain,
% 0.41/0.62      (![X0 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_B @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.62  thf('48', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.41/0.62      inference('demod', [status(thm)], ['32', '47'])).
% 0.41/0.62  thf('49', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['6', '48'])).
% 0.41/0.62  thf('50', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.41/0.62  thf(t75_xboole_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]:
% 0.41/0.62     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.41/0.62          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 0.41/0.62  thf('51', plain,
% 0.41/0.62      (![X18 : $i, X19 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X18 @ X19)
% 0.41/0.62          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X19))),
% 0.41/0.62      inference('cnf', [status(esa)], [t75_xboole_1])).
% 0.41/0.62  thf('52', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.41/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.62  thf('53', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['49', '52'])).
% 0.41/0.62  thf('54', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.62  thf('55', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.41/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.41/0.62  thf('56', plain,
% 0.41/0.62      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.41/0.62          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.41/0.62          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.41/0.62      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.41/0.62  thf('57', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.41/0.62          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.41/0.62  thf('58', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 0.41/0.62      inference('sup-', [status(thm)], ['3', '57'])).
% 0.41/0.62  thf('59', plain,
% 0.41/0.62      (![X2 : $i, X3 : $i]:
% 0.41/0.62         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.41/0.62  thf('60', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.41/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.41/0.62  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 0.41/0.62  
% 0.41/0.62  % SZS output end Refutation
% 0.41/0.62  
% 0.41/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
