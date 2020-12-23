%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V7HAa6Zb5K

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:31 EST 2020

% Result     : Theorem 4.09s
% Output     : Refutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 113 expanded)
%              Number of leaves         :   22 (  43 expanded)
%              Depth                    :   20
%              Number of atoms          :  547 ( 855 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
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
    r1_xboole_0 @ sk_B @ sk_C_1 ),
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
    ! [X32: $i,X33: $i] :
      ( ( ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) )
        = X32 )
      | ( r2_hidden @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ X21 )
      | ( ( k4_xboole_0 @ X19 @ X21 )
       != X19 ) ) ),
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

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('21',plain,(
    r1_tarski @ sk_C_1 @ sk_C_1 ),
    inference('sup+',[status(thm)],['19','20'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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

thf('25',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_tarski @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['6','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('37',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('41',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('45',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('55',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['53','54'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('56',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
      | ~ ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('60',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['0','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.V7HAa6Zb5K
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:00:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 4.09/4.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.09/4.28  % Solved by: fo/fo7.sh
% 4.09/4.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.09/4.28  % done 6670 iterations in 3.836s
% 4.09/4.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.09/4.28  % SZS output start Refutation
% 4.09/4.28  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.09/4.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.09/4.28  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(sk_B_type, type, sk_B: $i).
% 4.09/4.28  thf(sk_A_type, type, sk_A: $i).
% 4.09/4.28  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.09/4.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.09/4.28  thf(sk_D_type, type, sk_D: $i).
% 4.09/4.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.09/4.28  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.09/4.28  thf(t149_zfmisc_1, conjecture,
% 4.09/4.28    (![A:$i,B:$i,C:$i,D:$i]:
% 4.09/4.28     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.09/4.28         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.09/4.28       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.09/4.28  thf(zf_stmt_0, negated_conjecture,
% 4.09/4.28    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.09/4.28        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.09/4.28            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.09/4.28          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 4.09/4.28    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 4.09/4.28  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf(symmetry_r1_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.09/4.28  thf('2', plain,
% 4.09/4.28      (![X2 : $i, X3 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.09/4.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.09/4.28  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 4.09/4.28      inference('sup-', [status(thm)], ['1', '2'])).
% 4.09/4.28  thf('4', plain,
% 4.09/4.28      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf(commutativity_k3_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.09/4.28  thf('5', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.09/4.28  thf('6', plain,
% 4.09/4.28      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 4.09/4.28      inference('demod', [status(thm)], ['4', '5'])).
% 4.09/4.28  thf(t65_zfmisc_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 4.09/4.28       ( ~( r2_hidden @ B @ A ) ) ))).
% 4.09/4.28  thf('7', plain,
% 4.09/4.28      (![X32 : $i, X33 : $i]:
% 4.09/4.28         (((k4_xboole_0 @ X32 @ (k1_tarski @ X33)) = (X32))
% 4.09/4.28          | (r2_hidden @ X33 @ X32))),
% 4.09/4.28      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 4.09/4.28  thf(t83_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.09/4.28  thf('8', plain,
% 4.09/4.28      (![X19 : $i, X21 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X19 @ X21) | ((k4_xboole_0 @ X19 @ X21) != (X19)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.09/4.28  thf('9', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         (((X0) != (X0))
% 4.09/4.28          | (r2_hidden @ X1 @ X0)
% 4.09/4.28          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 4.09/4.28      inference('sup-', [status(thm)], ['7', '8'])).
% 4.09/4.28  thf('10', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 4.09/4.28      inference('simplify', [status(thm)], ['9'])).
% 4.09/4.28  thf('11', plain,
% 4.09/4.28      (![X2 : $i, X3 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.09/4.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.09/4.28  thf('12', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['10', '11'])).
% 4.09/4.28  thf('13', plain,
% 4.09/4.28      (![X19 : $i, X20 : $i]:
% 4.09/4.28         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 4.09/4.28      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.09/4.28  thf('14', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((r2_hidden @ X1 @ X0)
% 4.09/4.28          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 4.09/4.28      inference('sup-', [status(thm)], ['12', '13'])).
% 4.09/4.28  thf(t48_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.09/4.28  thf('15', plain,
% 4.09/4.28      (![X13 : $i, X14 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 4.09/4.28           = (k3_xboole_0 @ X13 @ X14))),
% 4.09/4.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.28  thf('16', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 4.09/4.28          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['14', '15'])).
% 4.09/4.28  thf('17', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf('18', plain,
% 4.09/4.28      (![X19 : $i, X20 : $i]:
% 4.09/4.28         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 4.09/4.28      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.09/4.28  thf('19', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['17', '18'])).
% 4.09/4.28  thf(t36_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.09/4.28  thf('20', plain,
% 4.09/4.28      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 4.09/4.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.09/4.28  thf('21', plain, ((r1_tarski @ sk_C_1 @ sk_C_1)),
% 4.09/4.28      inference('sup+', [status(thm)], ['19', '20'])).
% 4.09/4.28  thf(t85_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i,C:$i]:
% 4.09/4.28     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 4.09/4.28  thf('22', plain,
% 4.09/4.28      (![X22 : $i, X23 : $i, X24 : $i]:
% 4.09/4.28         (~ (r1_tarski @ X22 @ X23)
% 4.09/4.28          | (r1_xboole_0 @ X22 @ (k4_xboole_0 @ X24 @ X23)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t85_xboole_1])).
% 4.09/4.28  thf('23', plain,
% 4.09/4.28      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['21', '22'])).
% 4.09/4.28  thf('24', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 4.09/4.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.09/4.28  thf(t3_xboole_0, axiom,
% 4.09/4.28    (![A:$i,B:$i]:
% 4.09/4.28     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 4.09/4.28            ( r1_xboole_0 @ A @ B ) ) ) & 
% 4.09/4.28       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 4.09/4.28            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 4.09/4.28  thf('25', plain,
% 4.09/4.28      (![X4 : $i, X6 : $i, X7 : $i]:
% 4.09/4.28         (~ (r2_hidden @ X6 @ X4)
% 4.09/4.28          | ~ (r2_hidden @ X6 @ X7)
% 4.09/4.28          | ~ (r1_xboole_0 @ X4 @ X7))),
% 4.09/4.28      inference('cnf', [status(esa)], [t3_xboole_0])).
% 4.09/4.28  thf('26', plain,
% 4.09/4.28      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 4.09/4.28      inference('sup-', [status(thm)], ['24', '25'])).
% 4.09/4.28  thf('27', plain,
% 4.09/4.28      (![X0 : $i]: ~ (r2_hidden @ sk_D @ (k4_xboole_0 @ X0 @ sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['23', '26'])).
% 4.09/4.28  thf('28', plain,
% 4.09/4.28      (((k1_tarski @ sk_D) = (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['16', '27'])).
% 4.09/4.28  thf('29', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.09/4.28  thf('30', plain,
% 4.09/4.28      (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D)))),
% 4.09/4.28      inference('demod', [status(thm)], ['28', '29'])).
% 4.09/4.28  thf('31', plain,
% 4.09/4.28      (![X13 : $i, X14 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 4.09/4.28           = (k3_xboole_0 @ X13 @ X14))),
% 4.09/4.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.28  thf(t106_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i,C:$i]:
% 4.09/4.28     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.09/4.28       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 4.09/4.28  thf('32', plain,
% 4.09/4.28      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.09/4.28         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t106_xboole_1])).
% 4.09/4.28  thf('33', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.09/4.28         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['31', '32'])).
% 4.09/4.28  thf('34', plain,
% 4.09/4.28      (![X0 : $i]:
% 4.09/4.28         (~ (r1_tarski @ X0 @ (k1_tarski @ sk_D)) | (r1_tarski @ X0 @ sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['30', '33'])).
% 4.09/4.28  thf('35', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)),
% 4.09/4.28      inference('sup-', [status(thm)], ['6', '34'])).
% 4.09/4.28  thf('36', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['17', '18'])).
% 4.09/4.28  thf('37', plain,
% 4.09/4.28      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X8 @ X10)
% 4.09/4.28          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t106_xboole_1])).
% 4.09/4.28  thf('38', plain,
% 4.09/4.28      (![X0 : $i]: (~ (r1_tarski @ X0 @ sk_C_1) | (r1_xboole_0 @ X0 @ sk_B))),
% 4.09/4.28      inference('sup-', [status(thm)], ['36', '37'])).
% 4.09/4.28  thf('39', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 4.09/4.28      inference('sup-', [status(thm)], ['35', '38'])).
% 4.09/4.28  thf('40', plain,
% 4.09/4.28      (![X2 : $i, X3 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.09/4.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.09/4.28  thf('41', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 4.09/4.28      inference('sup-', [status(thm)], ['39', '40'])).
% 4.09/4.28  thf('42', plain,
% 4.09/4.28      (![X19 : $i, X20 : $i]:
% 4.09/4.28         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 4.09/4.28      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.09/4.28  thf('43', plain,
% 4.09/4.28      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.09/4.28      inference('sup-', [status(thm)], ['41', '42'])).
% 4.09/4.28  thf('44', plain,
% 4.09/4.28      (![X13 : $i, X14 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 4.09/4.28           = (k3_xboole_0 @ X13 @ X14))),
% 4.09/4.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.28  thf('45', plain,
% 4.09/4.28      (![X13 : $i, X14 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 4.09/4.28           = (k3_xboole_0 @ X13 @ X14))),
% 4.09/4.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.28  thf('46', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.09/4.28           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.09/4.28      inference('sup+', [status(thm)], ['44', '45'])).
% 4.09/4.28  thf('47', plain,
% 4.09/4.28      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.09/4.28      inference('demod', [status(thm)], ['43', '46'])).
% 4.09/4.28  thf('48', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.09/4.28      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.09/4.28  thf('49', plain,
% 4.09/4.28      (![X13 : $i, X14 : $i]:
% 4.09/4.28         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 4.09/4.28           = (k3_xboole_0 @ X13 @ X14))),
% 4.09/4.28      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.09/4.28  thf('50', plain,
% 4.09/4.28      (![X11 : $i, X12 : $i]: (r1_tarski @ (k4_xboole_0 @ X11 @ X12) @ X11)),
% 4.09/4.28      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.09/4.28  thf('51', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 4.09/4.28      inference('sup+', [status(thm)], ['49', '50'])).
% 4.09/4.28  thf('52', plain,
% 4.09/4.28      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 4.09/4.28      inference('sup+', [status(thm)], ['48', '51'])).
% 4.09/4.28  thf('53', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A))),
% 4.09/4.28      inference('sup+', [status(thm)], ['47', '52'])).
% 4.09/4.28  thf('54', plain,
% 4.09/4.28      (![X8 : $i, X9 : $i, X10 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X8 @ X10)
% 4.09/4.28          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 4.09/4.28      inference('cnf', [status(esa)], [t106_xboole_1])).
% 4.09/4.28  thf('55', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 4.09/4.28      inference('sup-', [status(thm)], ['53', '54'])).
% 4.09/4.28  thf(t70_xboole_1, axiom,
% 4.09/4.28    (![A:$i,B:$i,C:$i]:
% 4.09/4.28     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.09/4.28            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.09/4.28       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.09/4.28            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.09/4.28  thf('56', plain,
% 4.09/4.28      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 4.09/4.28          | ~ (r1_xboole_0 @ X15 @ X16)
% 4.09/4.28          | ~ (r1_xboole_0 @ X15 @ X17))),
% 4.09/4.28      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.09/4.28  thf('57', plain,
% 4.09/4.28      (![X0 : $i]:
% 4.09/4.28         (~ (r1_xboole_0 @ sk_B @ X0)
% 4.09/4.28          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 4.09/4.28      inference('sup-', [status(thm)], ['55', '56'])).
% 4.09/4.28  thf('58', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 4.09/4.28      inference('sup-', [status(thm)], ['3', '57'])).
% 4.09/4.28  thf('59', plain,
% 4.09/4.28      (![X2 : $i, X3 : $i]:
% 4.09/4.28         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.09/4.28      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.09/4.28  thf('60', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.09/4.28      inference('sup-', [status(thm)], ['58', '59'])).
% 4.09/4.28  thf('61', plain, ($false), inference('demod', [status(thm)], ['0', '60'])).
% 4.09/4.28  
% 4.09/4.28  % SZS output end Refutation
% 4.09/4.28  
% 4.09/4.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
