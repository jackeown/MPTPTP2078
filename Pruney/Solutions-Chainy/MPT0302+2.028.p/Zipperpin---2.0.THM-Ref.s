%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t5sFNKgvQ8

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:09 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 168 expanded)
%              Number of leaves         :   21 (  60 expanded)
%              Depth                    :   17
%              Number of atoms          :  577 (1412 expanded)
%              Number of equality atoms :   39 ( 137 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X3 @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ X2 @ X3 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t114_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ B @ A ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ B @ A ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t114_zfmisc_1])).

thf('6',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ sk_B )
      | ( ( k4_xboole_0 @ sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['0','14'])).

thf('16',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('19',plain,
    ( ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('23',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X16 @ X17 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X13: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X15 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_xboole_0 @ X4 @ X6 )
      | ( X4 = X6 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k1_xboole_0 = sk_B )
    | ( k1_xboole_0 = sk_A )
    | ( r2_hidden @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X21: $i,X22: $i,X23: $i,X25: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X25 ) )
      | ~ ( r2_hidden @ X23 @ X25 )
      | ~ ( r2_hidden @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','52'])).

thf('54',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_C_2 @ sk_B @ sk_A ) @ ( sk_C_2 @ sk_B @ k1_xboole_0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X23 ) @ ( k2_zfmisc_1 @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('57',plain,(
    r2_hidden @ ( sk_C_2 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_xboole_0 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('59',plain,(
    ~ ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('61',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.t5sFNKgvQ8
% 0.13/0.32  % Computer   : n017.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 17:13:16 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.32  % Python version: Python 3.6.8
% 0.13/0.33  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 520 iterations in 0.245s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.49/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.68  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.49/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(t3_boole, axiom,
% 0.49/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.68  thf('0', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.49/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.68  thf(d3_tarski, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( r1_tarski @ A @ B ) <=>
% 0.49/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.49/0.68  thf('1', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.68  thf(l54_zfmisc_1, axiom,
% 0.49/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.68     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.49/0.68       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.49/0.68         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 0.49/0.68          | ~ (r2_hidden @ X23 @ X25)
% 0.49/0.68          | ~ (r2_hidden @ X21 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X0 @ X1)
% 0.49/0.68          | ~ (r2_hidden @ X3 @ X2)
% 0.49/0.68          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.49/0.68             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('5', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X0 @ X1)
% 0.49/0.68          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X3 @ X2)) @ 
% 0.49/0.68             (k2_zfmisc_1 @ X0 @ X2))
% 0.49/0.68          | (r1_tarski @ X2 @ X3))),
% 0.49/0.68      inference('sup-', [status(thm)], ['1', '4'])).
% 0.49/0.68  thf(t114_zfmisc_1, conjecture,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.49/0.68       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.49/0.68         ( ( A ) = ( B ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i,B:$i]:
% 0.49/0.68        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ B @ A ) ) =>
% 0.49/0.68          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.49/0.68            ( ( A ) = ( B ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t114_zfmisc_1])).
% 0.49/0.68  thf('6', plain,
% 0.49/0.68      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.68         ((r2_hidden @ X21 @ X22)
% 0.49/0.68          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X24)))),
% 0.49/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.68  thf('8', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.49/0.68          | (r2_hidden @ X1 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         ((r1_tarski @ sk_B @ X0)
% 0.49/0.68          | (r1_tarski @ sk_A @ X1)
% 0.49/0.68          | (r2_hidden @ (sk_C @ X1 @ sk_A) @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['5', '8'])).
% 0.49/0.68  thf('10', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ sk_A @ sk_B)
% 0.49/0.68          | (r1_tarski @ sk_B @ X0)
% 0.49/0.68          | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['9', '10'])).
% 0.49/0.68  thf('12', plain,
% 0.49/0.68      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.68      inference('simplify', [status(thm)], ['11'])).
% 0.49/0.68  thf(l32_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.68  thf('13', plain,
% 0.49/0.68      (![X13 : $i, X15 : $i]:
% 0.49/0.68         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.49/0.68          | ~ (r1_tarski @ X13 @ X15))),
% 0.49/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.68  thf('14', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((r1_tarski @ sk_A @ sk_B)
% 0.49/0.68          | ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('15', plain, ((((sk_B) = (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.49/0.68      inference('sup+', [status(thm)], ['0', '14'])).
% 0.49/0.68  thf('16', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('17', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.49/0.68      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.49/0.68  thf(d8_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.49/0.68       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      (![X4 : $i, X6 : $i]:
% 0.49/0.68         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.49/0.68      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.49/0.68  thf('19', plain, ((((sk_A) = (sk_B)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.68  thf('20', plain, (((sk_A) != (sk_B))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('21', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.49/0.68      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.49/0.68  thf(t6_xboole_0, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.49/0.68          ( ![C:$i]:
% 0.49/0.68            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.49/0.68  thf('22', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i]:
% 0.49/0.68         (~ (r2_xboole_0 @ X11 @ X12)
% 0.49/0.68          | (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X12))),
% 0.49/0.68      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.49/0.68  thf('23', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_B)),
% 0.49/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.68  thf('24', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.49/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.49/0.68  thf(t48_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      (![X19 : $i, X20 : $i]:
% 0.49/0.68         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.49/0.68           = (k3_xboole_0 @ X19 @ X20))),
% 0.49/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.68      inference('sup+', [status(thm)], ['24', '25'])).
% 0.49/0.68  thf(t17_xboole_1, axiom,
% 0.49/0.68    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X16 : $i, X17 : $i]: (r1_tarski @ (k3_xboole_0 @ X16 @ X17) @ X16)),
% 0.49/0.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.49/0.68  thf('28', plain, (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X0)),
% 0.49/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.68  thf('30', plain,
% 0.49/0.68      (![X1 : $i, X3 : $i]:
% 0.49/0.68         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.49/0.68      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.49/0.68  thf('32', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.68      inference('simplify', [status(thm)], ['31'])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (![X13 : $i, X15 : $i]:
% 0.49/0.68         (((k4_xboole_0 @ X13 @ X15) = (k1_xboole_0))
% 0.49/0.68          | ~ (r1_tarski @ X13 @ X15))),
% 0.49/0.68      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.49/0.68  thf('34', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.68  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '34'])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (![X4 : $i, X6 : $i]:
% 0.49/0.68         ((r2_xboole_0 @ X4 @ X6) | ((X4) = (X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.49/0.68      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X0 : $i]: (((k1_xboole_0) = (X0)) | (r2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i]:
% 0.49/0.68         (~ (r2_xboole_0 @ X11 @ X12)
% 0.49/0.68          | (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X12))),
% 0.49/0.68      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (((k1_xboole_0) = (X0))
% 0.49/0.68          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (((k1_xboole_0) = (X0))
% 0.49/0.68          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('41', plain,
% 0.49/0.68      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.49/0.68         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 0.49/0.68          | ~ (r2_hidden @ X23 @ X25)
% 0.49/0.68          | ~ (r2_hidden @ X21 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((k1_xboole_0) = (X0))
% 0.49/0.68          | ~ (r2_hidden @ X2 @ X1)
% 0.49/0.68          | (r2_hidden @ (k4_tarski @ X2 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ 
% 0.49/0.68             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['40', '41'])).
% 0.49/0.68  thf('43', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((k1_xboole_0) = (X0))
% 0.49/0.68          | (r2_hidden @ 
% 0.49/0.68             (k4_tarski @ (sk_C_2 @ X0 @ k1_xboole_0) @ 
% 0.49/0.68              (sk_C_2 @ X1 @ k1_xboole_0)) @ 
% 0.49/0.68             (k2_zfmisc_1 @ X0 @ X1))
% 0.49/0.68          | ((k1_xboole_0) = (X1)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['39', '42'])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.68         ((r2_hidden @ X23 @ X24)
% 0.49/0.68          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X24)))),
% 0.49/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.68  thf('46', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.49/0.68          | (r2_hidden @ X0 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['44', '45'])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      ((((k1_xboole_0) = (sk_B))
% 0.49/0.68        | ((k1_xboole_0) = (sk_A))
% 0.49/0.68        | (r2_hidden @ (sk_C_2 @ sk_B @ k1_xboole_0) @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['43', '46'])).
% 0.49/0.68  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('49', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('50', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ k1_xboole_0) @ sk_A)),
% 0.49/0.68      inference('simplify_reflect-', [status(thm)], ['47', '48', '49'])).
% 0.49/0.68  thf('51', plain,
% 0.49/0.68      (![X21 : $i, X22 : $i, X23 : $i, X25 : $i]:
% 0.49/0.68         ((r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X25))
% 0.49/0.68          | ~ (r2_hidden @ X23 @ X25)
% 0.49/0.68          | ~ (r2_hidden @ X21 @ X22))),
% 0.49/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (r2_hidden @ X1 @ X0)
% 0.49/0.68          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C_2 @ sk_B @ k1_xboole_0)) @ 
% 0.49/0.68             (k2_zfmisc_1 @ X0 @ sk_A)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['50', '51'])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      ((r2_hidden @ 
% 0.49/0.68        (k4_tarski @ (sk_C_2 @ sk_B @ sk_A) @ (sk_C_2 @ sk_B @ k1_xboole_0)) @ 
% 0.49/0.68        (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['23', '52'])).
% 0.49/0.68  thf('54', plain,
% 0.49/0.68      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_B @ sk_A))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      ((r2_hidden @ 
% 0.49/0.68        (k4_tarski @ (sk_C_2 @ sk_B @ sk_A) @ (sk_C_2 @ sk_B @ k1_xboole_0)) @ 
% 0.49/0.68        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['53', '54'])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.49/0.68         ((r2_hidden @ X21 @ X22)
% 0.49/0.68          | ~ (r2_hidden @ (k4_tarski @ X21 @ X23) @ (k2_zfmisc_1 @ X22 @ X24)))),
% 0.49/0.68      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.49/0.68  thf('57', plain, ((r2_hidden @ (sk_C_2 @ sk_B @ sk_A) @ sk_A)),
% 0.49/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.49/0.68  thf('58', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i]:
% 0.49/0.68         (~ (r2_xboole_0 @ X11 @ X12)
% 0.49/0.68          | ~ (r2_hidden @ (sk_C_2 @ X12 @ X11) @ X11))),
% 0.49/0.68      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.49/0.68  thf('59', plain, (~ (r2_xboole_0 @ sk_A @ sk_B)),
% 0.49/0.68      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.68  thf('60', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.49/0.68      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.49/0.68  thf('61', plain, ($false), inference('demod', [status(thm)], ['59', '60'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
