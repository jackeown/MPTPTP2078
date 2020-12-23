%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Q5zQse99B

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:15 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 108 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :  534 ( 870 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t32_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( k7_subset_1 @ A @ B @ C )
              = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_subset_1])).

thf('0',plain,(
    ( k7_subset_1 @ sk_A @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( ( k7_subset_1 @ X23 @ X22 @ X24 )
        = ( k4_xboole_0 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ sk_A @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k9_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_subset_1 @ X19 @ X20 )
        = ( k4_xboole_0 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('7',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ( m1_subset_1 @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['7','15'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_subset_1 @ X27 @ X25 @ X26 )
        = ( k3_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r1_tarski @ X14 @ X12 )
      | ( X13
       != ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('25',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['23','25'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_A )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('34',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k5_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ X17 )
      | ( r2_hidden @ X16 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('41',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X7 @ X8 )
        = X7 )
      | ~ ( r1_tarski @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('45',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X4 @ X6 ) @ ( k3_xboole_0 @ X5 @ X6 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X4 @ X5 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = ( k3_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['34','50'])).

thf('52',plain,(
    ( k4_xboole_0 @ sk_B @ sk_C_1 )
 != ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['4','18','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Q5zQse99B
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:50:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.84/1.04  % Solved by: fo/fo7.sh
% 0.84/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.04  % done 862 iterations in 0.564s
% 0.84/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.84/1.04  % SZS output start Refutation
% 0.84/1.04  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.84/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.84/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.84/1.04  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.84/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.04  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.84/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.84/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.04  thf(t32_subset_1, conjecture,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ![C:$i]:
% 0.84/1.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04           ( ( k7_subset_1 @ A @ B @ C ) =
% 0.84/1.04             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.84/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.04    (~( ![A:$i,B:$i]:
% 0.84/1.04        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04          ( ![C:$i]:
% 0.84/1.04            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04              ( ( k7_subset_1 @ A @ B @ C ) =
% 0.84/1.04                ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.84/1.04    inference('cnf.neg', [status(esa)], [t32_subset_1])).
% 0.84/1.04  thf('0', plain,
% 0.84/1.04      (((k7_subset_1 @ sk_A @ sk_B @ sk_C_1)
% 0.84/1.04         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(redefinition_k7_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.84/1.04  thf('2', plain,
% 0.84/1.04      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 0.84/1.04          | ((k7_subset_1 @ X23 @ X22 @ X24) = (k4_xboole_0 @ X22 @ X24)))),
% 0.84/1.04      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.84/1.04  thf('3', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((k7_subset_1 @ sk_A @ sk_B @ X0) = (k4_xboole_0 @ sk_B @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['1', '2'])).
% 0.84/1.04  thf('4', plain,
% 0.84/1.04      (((k4_xboole_0 @ sk_B @ sk_C_1)
% 0.84/1.04         != (k9_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.84/1.04      inference('demod', [status(thm)], ['0', '3'])).
% 0.84/1.04  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf(d5_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.84/1.04  thf('6', plain,
% 0.84/1.04      (![X19 : $i, X20 : $i]:
% 0.84/1.04         (((k3_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))
% 0.84/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.84/1.04  thf('7', plain,
% 0.84/1.04      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.04  thf(t36_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.84/1.04  thf('8', plain,
% 0.84/1.04      (![X9 : $i, X10 : $i]: (r1_tarski @ (k4_xboole_0 @ X9 @ X10) @ X9)),
% 0.84/1.04      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.84/1.04  thf(d1_zfmisc_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.84/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.84/1.04  thf('9', plain,
% 0.84/1.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.84/1.04         (~ (r1_tarski @ X11 @ X12)
% 0.84/1.04          | (r2_hidden @ X11 @ X13)
% 0.84/1.04          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.84/1.04  thf('10', plain,
% 0.84/1.04      (![X11 : $i, X12 : $i]:
% 0.84/1.04         ((r2_hidden @ X11 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X11 @ X12))),
% 0.84/1.04      inference('simplify', [status(thm)], ['9'])).
% 0.84/1.04  thf('11', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.84/1.04      inference('sup-', [status(thm)], ['8', '10'])).
% 0.84/1.04  thf(d2_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( ( v1_xboole_0 @ A ) =>
% 0.84/1.04         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.84/1.04       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.84/1.04         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.84/1.04  thf('12', plain,
% 0.84/1.04      (![X16 : $i, X17 : $i]:
% 0.84/1.04         (~ (r2_hidden @ X16 @ X17)
% 0.84/1.04          | (m1_subset_1 @ X16 @ X17)
% 0.84/1.04          | (v1_xboole_0 @ X17))),
% 0.84/1.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.84/1.04  thf('13', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.84/1.04          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['11', '12'])).
% 0.84/1.04  thf(fc1_subset_1, axiom,
% 0.84/1.04    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.84/1.04  thf('14', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.84/1.04  thf('15', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.84/1.04      inference('clc', [status(thm)], ['13', '14'])).
% 0.84/1.04  thf('16', plain,
% 0.84/1.04      ((m1_subset_1 @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('sup+', [status(thm)], ['7', '15'])).
% 0.84/1.04  thf(redefinition_k9_subset_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.84/1.04       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.84/1.04  thf('17', plain,
% 0.84/1.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.84/1.04         (((k9_subset_1 @ X27 @ X25 @ X26) = (k3_xboole_0 @ X25 @ X26))
% 0.84/1.04          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27)))),
% 0.84/1.04      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.84/1.04  thf('18', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((k9_subset_1 @ sk_A @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.84/1.04           = (k3_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['16', '17'])).
% 0.84/1.04  thf('19', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('20', plain,
% 0.84/1.04      (![X16 : $i, X17 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X16 @ X17)
% 0.84/1.04          | (r2_hidden @ X16 @ X17)
% 0.84/1.04          | (v1_xboole_0 @ X17))),
% 0.84/1.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.84/1.04  thf('21', plain,
% 0.84/1.04      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.84/1.04        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['19', '20'])).
% 0.84/1.04  thf('22', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.84/1.04  thf('23', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('clc', [status(thm)], ['21', '22'])).
% 0.84/1.04  thf('24', plain,
% 0.84/1.04      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.04         (~ (r2_hidden @ X14 @ X13)
% 0.84/1.04          | (r1_tarski @ X14 @ X12)
% 0.84/1.04          | ((X13) != (k1_zfmisc_1 @ X12)))),
% 0.84/1.04      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.84/1.04  thf('25', plain,
% 0.84/1.04      (![X12 : $i, X14 : $i]:
% 0.84/1.04         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['24'])).
% 0.84/1.04  thf('26', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.84/1.04      inference('sup-', [status(thm)], ['23', '25'])).
% 0.84/1.04  thf(t28_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.84/1.04  thf('27', plain,
% 0.84/1.04      (![X7 : $i, X8 : $i]:
% 0.84/1.04         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.84/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.04  thf('28', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) = (sk_C_1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['26', '27'])).
% 0.84/1.04  thf(commutativity_k3_xboole_0, axiom,
% 0.84/1.04    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.84/1.04  thf('29', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.04  thf(t100_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i]:
% 0.84/1.04     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.84/1.04  thf('30', plain,
% 0.84/1.04      (![X2 : $i, X3 : $i]:
% 0.84/1.04         ((k4_xboole_0 @ X2 @ X3)
% 0.84/1.04           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.84/1.04      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.84/1.04  thf('31', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((k4_xboole_0 @ X0 @ X1)
% 0.84/1.04           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['29', '30'])).
% 0.84/1.04  thf('32', plain,
% 0.84/1.04      (((k4_xboole_0 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.04      inference('sup+', [status(thm)], ['28', '31'])).
% 0.84/1.04  thf('33', plain,
% 0.84/1.04      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.04      inference('sup-', [status(thm)], ['5', '6'])).
% 0.84/1.04  thf('34', plain,
% 0.84/1.04      (((k3_subset_1 @ sk_A @ sk_C_1) = (k5_xboole_0 @ sk_A @ sk_C_1))),
% 0.84/1.04      inference('sup+', [status(thm)], ['32', '33'])).
% 0.84/1.04  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.04  thf('36', plain,
% 0.84/1.04      (![X16 : $i, X17 : $i]:
% 0.84/1.04         (~ (m1_subset_1 @ X16 @ X17)
% 0.84/1.04          | (r2_hidden @ X16 @ X17)
% 0.84/1.04          | (v1_xboole_0 @ X17))),
% 0.84/1.04      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.84/1.04  thf('37', plain,
% 0.84/1.04      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.84/1.04        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.84/1.04      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.04  thf('38', plain, (![X21 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X21))),
% 0.84/1.04      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.84/1.04  thf('39', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.84/1.04      inference('clc', [status(thm)], ['37', '38'])).
% 0.84/1.04  thf('40', plain,
% 0.84/1.04      (![X12 : $i, X14 : $i]:
% 0.84/1.04         ((r1_tarski @ X14 @ X12) | ~ (r2_hidden @ X14 @ (k1_zfmisc_1 @ X12)))),
% 0.84/1.04      inference('simplify', [status(thm)], ['24'])).
% 0.84/1.04  thf('41', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.84/1.04      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.04  thf('42', plain,
% 0.84/1.04      (![X7 : $i, X8 : $i]:
% 0.84/1.04         (((k3_xboole_0 @ X7 @ X8) = (X7)) | ~ (r1_tarski @ X7 @ X8))),
% 0.84/1.04      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.84/1.04  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.84/1.04      inference('sup-', [status(thm)], ['41', '42'])).
% 0.84/1.04  thf('44', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.04  thf(t112_xboole_1, axiom,
% 0.84/1.04    (![A:$i,B:$i,C:$i]:
% 0.84/1.04     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.84/1.04       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 0.84/1.04  thf('45', plain,
% 0.84/1.04      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.84/1.04         ((k5_xboole_0 @ (k3_xboole_0 @ X4 @ X6) @ (k3_xboole_0 @ X5 @ X6))
% 0.84/1.04           = (k3_xboole_0 @ (k5_xboole_0 @ X4 @ X5) @ X6))),
% 0.84/1.04      inference('cnf', [status(esa)], [t112_xboole_1])).
% 0.84/1.04  thf('46', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.84/1.04         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 0.84/1.04           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 0.84/1.04      inference('sup+', [status(thm)], ['44', '45'])).
% 0.84/1.04  thf('47', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 0.84/1.04           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.84/1.04      inference('sup+', [status(thm)], ['43', '46'])).
% 0.84/1.04  thf('48', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]:
% 0.84/1.04         ((k4_xboole_0 @ X0 @ X1)
% 0.84/1.04           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['29', '30'])).
% 0.84/1.04  thf('49', plain,
% 0.84/1.04      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.84/1.04      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.84/1.04  thf('50', plain,
% 0.84/1.04      (![X0 : $i]:
% 0.84/1.04         ((k4_xboole_0 @ sk_B @ X0)
% 0.84/1.04           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 0.84/1.04      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.84/1.04  thf('51', plain,
% 0.84/1.04      (((k4_xboole_0 @ sk_B @ sk_C_1)
% 0.84/1.04         = (k3_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.84/1.04      inference('sup+', [status(thm)], ['34', '50'])).
% 0.84/1.04  thf('52', plain,
% 0.84/1.04      (((k4_xboole_0 @ sk_B @ sk_C_1) != (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.84/1.04      inference('demod', [status(thm)], ['4', '18', '51'])).
% 0.84/1.04  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.84/1.04  
% 0.84/1.04  % SZS output end Refutation
% 0.84/1.04  
% 0.84/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
