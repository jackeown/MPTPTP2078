%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7OcHVCvJd

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 4.60s
% Output     : Refutation 4.60s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 118 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  552 ( 861 expanded)
%              Number of equality atoms :   33 (  42 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('15',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('24',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X26 @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ~ ( r1_tarski @ X14 @ ( k4_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','30'])).

thf('32',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('34',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['41','46'])).

thf('48',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['40','47'])).

thf('49',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['13','14'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k4_xboole_0 @ X28 @ X29 )
        = X28 )
      | ~ ( r1_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_C_1 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['48','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('58',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7OcHVCvJd
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:45:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.60/4.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.60/4.83  % Solved by: fo/fo7.sh
% 4.60/4.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.60/4.83  % done 6063 iterations in 4.378s
% 4.60/4.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.60/4.83  % SZS output start Refutation
% 4.60/4.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.60/4.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.60/4.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.60/4.83  thf(sk_D_1_type, type, sk_D_1: $i).
% 4.60/4.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.60/4.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.60/4.83  thf(sk_A_type, type, sk_A: $i).
% 4.60/4.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.60/4.83  thf(sk_B_type, type, sk_B: $i).
% 4.60/4.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.60/4.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.60/4.83  thf(t149_zfmisc_1, conjecture,
% 4.60/4.83    (![A:$i,B:$i,C:$i,D:$i]:
% 4.60/4.83     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.60/4.83         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.60/4.83       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.60/4.83  thf(zf_stmt_0, negated_conjecture,
% 4.60/4.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.60/4.83        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 4.60/4.83            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 4.60/4.83          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 4.60/4.83    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 4.60/4.83  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.60/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.83  thf('1', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 4.60/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.83  thf(l27_zfmisc_1, axiom,
% 4.60/4.83    (![A:$i,B:$i]:
% 4.60/4.83     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 4.60/4.83  thf('2', plain,
% 4.60/4.83      (![X37 : $i, X38 : $i]:
% 4.60/4.83         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 4.60/4.83      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 4.60/4.83  thf(t83_xboole_1, axiom,
% 4.60/4.83    (![A:$i,B:$i]:
% 4.60/4.83     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.60/4.83  thf('3', plain,
% 4.60/4.83      (![X28 : $i, X29 : $i]:
% 4.60/4.83         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 4.60/4.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.60/4.83  thf('4', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]:
% 4.60/4.83         ((r2_hidden @ X1 @ X0)
% 4.60/4.83          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 4.60/4.83      inference('sup-', [status(thm)], ['2', '3'])).
% 4.60/4.83  thf(t48_xboole_1, axiom,
% 4.60/4.83    (![A:$i,B:$i]:
% 4.60/4.83     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.60/4.83  thf('5', plain,
% 4.60/4.83      (![X17 : $i, X18 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 4.60/4.83           = (k3_xboole_0 @ X17 @ X18))),
% 4.60/4.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.60/4.83  thf('6', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]:
% 4.60/4.83         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 4.60/4.83          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 4.60/4.83      inference('sup+', [status(thm)], ['4', '5'])).
% 4.60/4.83  thf(d5_xboole_0, axiom,
% 4.60/4.83    (![A:$i,B:$i,C:$i]:
% 4.60/4.83     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 4.60/4.83       ( ![D:$i]:
% 4.60/4.83         ( ( r2_hidden @ D @ C ) <=>
% 4.60/4.83           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 4.60/4.83  thf('7', plain,
% 4.60/4.83      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 4.60/4.83         (~ (r2_hidden @ X6 @ X5)
% 4.60/4.83          | ~ (r2_hidden @ X6 @ X4)
% 4.60/4.83          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 4.60/4.83      inference('cnf', [status(esa)], [d5_xboole_0])).
% 4.60/4.83  thf('8', plain,
% 4.60/4.83      (![X3 : $i, X4 : $i, X6 : $i]:
% 4.60/4.83         (~ (r2_hidden @ X6 @ X4)
% 4.60/4.83          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 4.60/4.83      inference('simplify', [status(thm)], ['7'])).
% 4.60/4.83  thf('9', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]:
% 4.60/4.83         (((k1_tarski @ X1) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 4.60/4.83          | ~ (r2_hidden @ X1 @ X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['6', '8'])).
% 4.60/4.83  thf('10', plain,
% 4.60/4.83      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1))),
% 4.60/4.83      inference('sup-', [status(thm)], ['1', '9'])).
% 4.60/4.83  thf(commutativity_k3_xboole_0, axiom,
% 4.60/4.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.60/4.83  thf('11', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.60/4.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.60/4.83  thf('12', plain,
% 4.60/4.83      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)))),
% 4.60/4.83      inference('demod', [status(thm)], ['10', '11'])).
% 4.60/4.83  thf('13', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 4.60/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.83  thf(symmetry_r1_xboole_0, axiom,
% 4.60/4.83    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.60/4.83  thf('14', plain,
% 4.60/4.83      (![X8 : $i, X9 : $i]:
% 4.60/4.83         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 4.60/4.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.60/4.83  thf('15', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 4.60/4.83      inference('sup-', [status(thm)], ['13', '14'])).
% 4.60/4.83  thf(t74_xboole_1, axiom,
% 4.60/4.83    (![A:$i,B:$i,C:$i]:
% 4.60/4.83     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 4.60/4.83          ( r1_xboole_0 @ A @ B ) ) ))).
% 4.60/4.83  thf('16', plain,
% 4.60/4.83      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.60/4.83         (~ (r1_xboole_0 @ X23 @ X24)
% 4.60/4.83          | (r1_xboole_0 @ X23 @ (k3_xboole_0 @ X24 @ X25)))),
% 4.60/4.83      inference('cnf', [status(esa)], [t74_xboole_1])).
% 4.60/4.83  thf('17', plain,
% 4.60/4.83      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['15', '16'])).
% 4.60/4.83  thf('18', plain,
% 4.60/4.83      (![X28 : $i, X29 : $i]:
% 4.60/4.83         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 4.60/4.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.60/4.83  thf('19', plain,
% 4.60/4.83      (![X0 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)) = (sk_B))),
% 4.60/4.83      inference('sup-', [status(thm)], ['17', '18'])).
% 4.60/4.83  thf('20', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)) = (sk_B))),
% 4.60/4.83      inference('sup+', [status(thm)], ['12', '19'])).
% 4.60/4.83  thf('21', plain,
% 4.60/4.83      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 4.60/4.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.60/4.83  thf('22', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.60/4.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.60/4.83  thf('23', plain,
% 4.60/4.83      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 4.60/4.83      inference('demod', [status(thm)], ['21', '22'])).
% 4.60/4.83  thf(t79_xboole_1, axiom,
% 4.60/4.83    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 4.60/4.83  thf('24', plain,
% 4.60/4.83      (![X26 : $i, X27 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X26 @ X27) @ X27)),
% 4.60/4.83      inference('cnf', [status(esa)], [t79_xboole_1])).
% 4.60/4.83  thf('25', plain,
% 4.60/4.83      (![X8 : $i, X9 : $i]:
% 4.60/4.83         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 4.60/4.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.60/4.83  thf('26', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['24', '25'])).
% 4.60/4.83  thf('27', plain,
% 4.60/4.83      (![X28 : $i, X29 : $i]:
% 4.60/4.83         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 4.60/4.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.60/4.83  thf('28', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['26', '27'])).
% 4.60/4.83  thf(t106_xboole_1, axiom,
% 4.60/4.83    (![A:$i,B:$i,C:$i]:
% 4.60/4.83     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.60/4.83       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 4.60/4.83  thf('29', plain,
% 4.60/4.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.60/4.83         ((r1_xboole_0 @ X14 @ X16)
% 4.60/4.83          | ~ (r1_tarski @ X14 @ (k4_xboole_0 @ X15 @ X16)))),
% 4.60/4.83      inference('cnf', [status(esa)], [t106_xboole_1])).
% 4.60/4.83  thf('30', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.83         (~ (r1_tarski @ X2 @ X0)
% 4.60/4.83          | (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.60/4.83      inference('sup-', [status(thm)], ['28', '29'])).
% 4.60/4.83  thf('31', plain,
% 4.60/4.83      (![X0 : $i]:
% 4.60/4.83         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 4.60/4.83          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D_1)))),
% 4.60/4.83      inference('sup-', [status(thm)], ['23', '30'])).
% 4.60/4.83  thf('32', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 4.60/4.83      inference('sup+', [status(thm)], ['20', '31'])).
% 4.60/4.83  thf('33', plain,
% 4.60/4.83      (![X8 : $i, X9 : $i]:
% 4.60/4.83         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 4.60/4.83      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.60/4.83  thf('34', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 4.60/4.83      inference('sup-', [status(thm)], ['32', '33'])).
% 4.60/4.83  thf('35', plain,
% 4.60/4.83      (![X28 : $i, X29 : $i]:
% 4.60/4.83         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 4.60/4.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.60/4.83  thf('36', plain,
% 4.60/4.83      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.60/4.83      inference('sup-', [status(thm)], ['34', '35'])).
% 4.60/4.83  thf('37', plain,
% 4.60/4.83      (![X17 : $i, X18 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 4.60/4.83           = (k3_xboole_0 @ X17 @ X18))),
% 4.60/4.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.60/4.83  thf('38', plain,
% 4.60/4.83      (![X17 : $i, X18 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 4.60/4.83           = (k3_xboole_0 @ X17 @ X18))),
% 4.60/4.83      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.60/4.83  thf('39', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 4.60/4.83           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 4.60/4.83      inference('sup+', [status(thm)], ['37', '38'])).
% 4.60/4.83  thf('40', plain,
% 4.60/4.83      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 4.60/4.83      inference('demod', [status(thm)], ['36', '39'])).
% 4.60/4.83  thf('41', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.60/4.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.60/4.83  thf('42', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['24', '25'])).
% 4.60/4.83  thf('43', plain,
% 4.60/4.83      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.60/4.83         (~ (r1_xboole_0 @ X23 @ X24)
% 4.60/4.83          | (r1_xboole_0 @ X23 @ (k3_xboole_0 @ X24 @ X25)))),
% 4.60/4.83      inference('cnf', [status(esa)], [t74_xboole_1])).
% 4.60/4.83  thf('44', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.83         (r1_xboole_0 @ X0 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 4.60/4.83      inference('sup-', [status(thm)], ['42', '43'])).
% 4.60/4.83  thf('45', plain,
% 4.60/4.83      (![X28 : $i, X29 : $i]:
% 4.60/4.83         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 4.60/4.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.60/4.83  thf('46', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 4.60/4.83           = (X1))),
% 4.60/4.83      inference('sup-', [status(thm)], ['44', '45'])).
% 4.60/4.83  thf('47', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 4.60/4.83           = (X0))),
% 4.60/4.83      inference('sup+', [status(thm)], ['41', '46'])).
% 4.60/4.83  thf('48', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 4.60/4.83      inference('sup+', [status(thm)], ['40', '47'])).
% 4.60/4.83  thf('49', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 4.60/4.83      inference('sup-', [status(thm)], ['13', '14'])).
% 4.60/4.83  thf('50', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['24', '25'])).
% 4.60/4.83  thf(t70_xboole_1, axiom,
% 4.60/4.83    (![A:$i,B:$i,C:$i]:
% 4.60/4.83     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.60/4.83            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.60/4.83       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.60/4.83            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.60/4.83  thf('51', plain,
% 4.60/4.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.60/4.83         ((r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.60/4.83          | ~ (r1_xboole_0 @ X19 @ X20)
% 4.60/4.83          | ~ (r1_xboole_0 @ X19 @ X21))),
% 4.60/4.83      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.60/4.83  thf('52', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.60/4.83         (~ (r1_xboole_0 @ X0 @ X2)
% 4.60/4.83          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)))),
% 4.60/4.83      inference('sup-', [status(thm)], ['50', '51'])).
% 4.60/4.83  thf('53', plain,
% 4.60/4.83      (![X0 : $i]:
% 4.60/4.83         (r1_xboole_0 @ sk_B @ 
% 4.60/4.83          (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_1))),
% 4.60/4.83      inference('sup-', [status(thm)], ['49', '52'])).
% 4.60/4.83  thf('54', plain,
% 4.60/4.83      (![X28 : $i, X29 : $i]:
% 4.60/4.83         (((k4_xboole_0 @ X28 @ X29) = (X28)) | ~ (r1_xboole_0 @ X28 @ X29))),
% 4.60/4.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 4.60/4.83  thf('55', plain,
% 4.60/4.83      (![X0 : $i]:
% 4.60/4.83         ((k4_xboole_0 @ sk_B @ 
% 4.60/4.83           (k2_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_C_1)) = (sk_B))),
% 4.60/4.83      inference('sup-', [status(thm)], ['53', '54'])).
% 4.60/4.83  thf('56', plain,
% 4.60/4.83      (((k4_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1)) = (sk_B))),
% 4.60/4.83      inference('sup+', [status(thm)], ['48', '55'])).
% 4.60/4.83  thf('57', plain,
% 4.60/4.83      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 4.60/4.83      inference('sup-', [status(thm)], ['24', '25'])).
% 4.60/4.83  thf('58', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 4.60/4.83      inference('sup+', [status(thm)], ['56', '57'])).
% 4.60/4.83  thf('59', plain, ($false), inference('demod', [status(thm)], ['0', '58'])).
% 4.60/4.83  
% 4.60/4.83  % SZS output end Refutation
% 4.60/4.83  
% 4.60/4.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
