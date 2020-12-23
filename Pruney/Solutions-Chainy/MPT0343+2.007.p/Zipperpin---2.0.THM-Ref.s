%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXhmgKfNvO

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:37 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 111 expanded)
%              Number of leaves         :   19 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :  583 ( 977 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r1_tarski @ X18 @ X16 )
      | ( X17
       != ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( m1_subset_1 @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B_1 )
      | ( r2_hidden @ X24 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X24 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_C_2 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_C_2 )
    | ( r1_tarski @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference(simplify,[status(thm)],['21'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X21 )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X23: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X18 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('34',plain,(
    r1_tarski @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ X20 @ X21 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_C_2 )
      | ( r2_hidden @ X24 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X24 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( r1_tarski @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_C_2
        = ( k3_xboole_0 @ X0 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_C_2 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('51',plain,(
    ! [X8: $i,X9: $i,X12: $i] :
      ( ( X12
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X9 )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X12 @ X9 @ X8 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['25'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_C_2
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['49','55'])).

thf('57',plain,
    ( sk_C_2
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    sk_C_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['24','57'])).

thf('59',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vXhmgKfNvO
% 0.14/0.37  % Computer   : n011.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 16:24:27 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 1.30/1.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.30/1.47  % Solved by: fo/fo7.sh
% 1.30/1.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.30/1.47  % done 1948 iterations in 1.013s
% 1.30/1.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.30/1.47  % SZS output start Refutation
% 1.30/1.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.30/1.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.30/1.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.30/1.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.30/1.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.30/1.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.30/1.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.30/1.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.30/1.47  thf(sk_A_type, type, sk_A: $i).
% 1.30/1.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.30/1.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.30/1.47  thf(d3_tarski, axiom,
% 1.30/1.47    (![A:$i,B:$i]:
% 1.30/1.47     ( ( r1_tarski @ A @ B ) <=>
% 1.30/1.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.30/1.47  thf('0', plain,
% 1.30/1.47      (![X4 : $i, X6 : $i]:
% 1.30/1.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf(t8_subset_1, conjecture,
% 1.30/1.47    (![A:$i,B:$i]:
% 1.30/1.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.30/1.47       ( ![C:$i]:
% 1.30/1.47         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.30/1.47           ( ( ![D:$i]:
% 1.30/1.47               ( ( m1_subset_1 @ D @ A ) =>
% 1.30/1.47                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 1.30/1.47             ( ( B ) = ( C ) ) ) ) ) ))).
% 1.30/1.47  thf(zf_stmt_0, negated_conjecture,
% 1.30/1.47    (~( ![A:$i,B:$i]:
% 1.30/1.47        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.30/1.47          ( ![C:$i]:
% 1.30/1.47            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.30/1.47              ( ( ![D:$i]:
% 1.30/1.47                  ( ( m1_subset_1 @ D @ A ) =>
% 1.30/1.47                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 1.30/1.47                ( ( B ) = ( C ) ) ) ) ) ) )),
% 1.30/1.47    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 1.30/1.47  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.30/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.47  thf(d2_subset_1, axiom,
% 1.30/1.47    (![A:$i,B:$i]:
% 1.30/1.47     ( ( ( v1_xboole_0 @ A ) =>
% 1.30/1.47         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.30/1.47       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.30/1.47         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.30/1.47  thf('2', plain,
% 1.30/1.47      (![X20 : $i, X21 : $i]:
% 1.30/1.47         (~ (m1_subset_1 @ X20 @ X21)
% 1.30/1.47          | (r2_hidden @ X20 @ X21)
% 1.30/1.47          | (v1_xboole_0 @ X21))),
% 1.30/1.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.30/1.47  thf('3', plain,
% 1.30/1.47      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.30/1.47        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 1.30/1.47      inference('sup-', [status(thm)], ['1', '2'])).
% 1.30/1.47  thf(fc1_subset_1, axiom,
% 1.30/1.47    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.30/1.47  thf('4', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 1.30/1.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.30/1.47  thf('5', plain, ((r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 1.30/1.47      inference('clc', [status(thm)], ['3', '4'])).
% 1.30/1.47  thf(d1_zfmisc_1, axiom,
% 1.30/1.47    (![A:$i,B:$i]:
% 1.30/1.47     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.30/1.47       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.30/1.47  thf('6', plain,
% 1.30/1.47      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X18 @ X17)
% 1.30/1.47          | (r1_tarski @ X18 @ X16)
% 1.30/1.47          | ((X17) != (k1_zfmisc_1 @ X16)))),
% 1.30/1.47      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.30/1.47  thf('7', plain,
% 1.30/1.47      (![X16 : $i, X18 : $i]:
% 1.30/1.47         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 1.30/1.47      inference('simplify', [status(thm)], ['6'])).
% 1.30/1.47  thf('8', plain, ((r1_tarski @ sk_B_1 @ sk_A)),
% 1.30/1.47      inference('sup-', [status(thm)], ['5', '7'])).
% 1.30/1.47  thf('9', plain,
% 1.30/1.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X3 @ X4)
% 1.30/1.47          | (r2_hidden @ X3 @ X5)
% 1.30/1.47          | ~ (r1_tarski @ X4 @ X5))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('10', plain,
% 1.30/1.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.30/1.47      inference('sup-', [status(thm)], ['8', '9'])).
% 1.30/1.47  thf('11', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 1.30/1.47      inference('sup-', [status(thm)], ['0', '10'])).
% 1.30/1.47  thf('12', plain,
% 1.30/1.47      (![X20 : $i, X21 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X20 @ X21)
% 1.30/1.47          | (m1_subset_1 @ X20 @ X21)
% 1.30/1.47          | (v1_xboole_0 @ X21))),
% 1.30/1.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.30/1.47  thf(d1_xboole_0, axiom,
% 1.30/1.47    (![A:$i]:
% 1.30/1.47     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.30/1.47  thf('13', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.30/1.47      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.30/1.47  thf('14', plain,
% 1.30/1.47      (![X20 : $i, X21 : $i]:
% 1.30/1.47         ((m1_subset_1 @ X20 @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 1.30/1.47      inference('clc', [status(thm)], ['12', '13'])).
% 1.30/1.47  thf('15', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r1_tarski @ sk_B_1 @ X0)
% 1.30/1.47          | (m1_subset_1 @ (sk_C @ X0 @ sk_B_1) @ sk_A))),
% 1.30/1.47      inference('sup-', [status(thm)], ['11', '14'])).
% 1.30/1.47  thf('16', plain,
% 1.30/1.47      (![X24 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X24 @ sk_B_1)
% 1.30/1.47          | (r2_hidden @ X24 @ sk_C_2)
% 1.30/1.47          | ~ (m1_subset_1 @ X24 @ sk_A))),
% 1.30/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.47  thf('17', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r1_tarski @ sk_B_1 @ X0)
% 1.30/1.47          | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)
% 1.30/1.47          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_B_1))),
% 1.30/1.47      inference('sup-', [status(thm)], ['15', '16'])).
% 1.30/1.47  thf('18', plain,
% 1.30/1.47      (![X4 : $i, X6 : $i]:
% 1.30/1.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('19', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_C_2)
% 1.30/1.47          | (r1_tarski @ sk_B_1 @ X0))),
% 1.30/1.47      inference('clc', [status(thm)], ['17', '18'])).
% 1.30/1.47  thf('20', plain,
% 1.30/1.47      (![X4 : $i, X6 : $i]:
% 1.30/1.47         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('21', plain,
% 1.30/1.47      (((r1_tarski @ sk_B_1 @ sk_C_2) | (r1_tarski @ sk_B_1 @ sk_C_2))),
% 1.30/1.47      inference('sup-', [status(thm)], ['19', '20'])).
% 1.30/1.47  thf('22', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 1.30/1.47      inference('simplify', [status(thm)], ['21'])).
% 1.30/1.47  thf(t28_xboole_1, axiom,
% 1.30/1.47    (![A:$i,B:$i]:
% 1.30/1.47     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.30/1.47  thf('23', plain,
% 1.30/1.47      (![X13 : $i, X14 : $i]:
% 1.30/1.47         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 1.30/1.47      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.30/1.47  thf('24', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 1.30/1.47      inference('sup-', [status(thm)], ['22', '23'])).
% 1.30/1.47  thf(d4_xboole_0, axiom,
% 1.30/1.47    (![A:$i,B:$i,C:$i]:
% 1.30/1.47     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.30/1.47       ( ![D:$i]:
% 1.30/1.47         ( ( r2_hidden @ D @ C ) <=>
% 1.30/1.47           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.30/1.47  thf('25', plain,
% 1.30/1.47      (![X8 : $i, X9 : $i, X12 : $i]:
% 1.30/1.47         (((X12) = (k3_xboole_0 @ X8 @ X9))
% 1.30/1.47          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X9)
% 1.30/1.47          | (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X12))),
% 1.30/1.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.30/1.47  thf('26', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]:
% 1.30/1.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.30/1.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.47      inference('eq_fact', [status(thm)], ['25'])).
% 1.30/1.47  thf('27', plain,
% 1.30/1.47      (![X4 : $i, X6 : $i]:
% 1.30/1.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('28', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.30/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.47  thf('29', plain,
% 1.30/1.47      (![X20 : $i, X21 : $i]:
% 1.30/1.47         (~ (m1_subset_1 @ X20 @ X21)
% 1.30/1.47          | (r2_hidden @ X20 @ X21)
% 1.30/1.47          | (v1_xboole_0 @ X21))),
% 1.30/1.47      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.30/1.47  thf('30', plain,
% 1.30/1.47      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.30/1.47        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 1.30/1.47      inference('sup-', [status(thm)], ['28', '29'])).
% 1.30/1.47  thf('31', plain, (![X23 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X23))),
% 1.30/1.47      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.30/1.47  thf('32', plain, ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.30/1.47      inference('clc', [status(thm)], ['30', '31'])).
% 1.30/1.47  thf('33', plain,
% 1.30/1.47      (![X16 : $i, X18 : $i]:
% 1.30/1.47         ((r1_tarski @ X18 @ X16) | ~ (r2_hidden @ X18 @ (k1_zfmisc_1 @ X16)))),
% 1.30/1.47      inference('simplify', [status(thm)], ['6'])).
% 1.30/1.47  thf('34', plain, ((r1_tarski @ sk_C_2 @ sk_A)),
% 1.30/1.47      inference('sup-', [status(thm)], ['32', '33'])).
% 1.30/1.47  thf('35', plain,
% 1.30/1.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X3 @ X4)
% 1.30/1.47          | (r2_hidden @ X3 @ X5)
% 1.30/1.47          | ~ (r1_tarski @ X4 @ X5))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('36', plain,
% 1.30/1.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.30/1.47      inference('sup-', [status(thm)], ['34', '35'])).
% 1.30/1.47  thf('37', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r1_tarski @ sk_C_2 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 1.30/1.47      inference('sup-', [status(thm)], ['27', '36'])).
% 1.30/1.47  thf('38', plain,
% 1.30/1.47      (![X20 : $i, X21 : $i]:
% 1.30/1.47         ((m1_subset_1 @ X20 @ X21) | ~ (r2_hidden @ X20 @ X21))),
% 1.30/1.47      inference('clc', [status(thm)], ['12', '13'])).
% 1.30/1.47  thf('39', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r1_tarski @ sk_C_2 @ X0)
% 1.30/1.47          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ sk_A))),
% 1.30/1.47      inference('sup-', [status(thm)], ['37', '38'])).
% 1.30/1.47  thf('40', plain,
% 1.30/1.47      (![X24 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X24 @ sk_C_2)
% 1.30/1.47          | (r2_hidden @ X24 @ sk_B_1)
% 1.30/1.47          | ~ (m1_subset_1 @ X24 @ sk_A))),
% 1.30/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.47  thf('41', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r1_tarski @ sk_C_2 @ X0)
% 1.30/1.47          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 1.30/1.47          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 1.30/1.47      inference('sup-', [status(thm)], ['39', '40'])).
% 1.30/1.47  thf('42', plain,
% 1.30/1.47      (![X4 : $i, X6 : $i]:
% 1.30/1.47         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('43', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 1.30/1.47          | (r1_tarski @ sk_C_2 @ X0))),
% 1.30/1.47      inference('clc', [status(thm)], ['41', '42'])).
% 1.30/1.47  thf('44', plain,
% 1.30/1.47      (![X4 : $i, X6 : $i]:
% 1.30/1.47         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('45', plain,
% 1.30/1.47      (((r1_tarski @ sk_C_2 @ sk_B_1) | (r1_tarski @ sk_C_2 @ sk_B_1))),
% 1.30/1.47      inference('sup-', [status(thm)], ['43', '44'])).
% 1.30/1.47  thf('46', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 1.30/1.47      inference('simplify', [status(thm)], ['45'])).
% 1.30/1.47  thf('47', plain,
% 1.30/1.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.30/1.47         (~ (r2_hidden @ X3 @ X4)
% 1.30/1.47          | (r2_hidden @ X3 @ X5)
% 1.30/1.47          | ~ (r1_tarski @ X4 @ X5))),
% 1.30/1.47      inference('cnf', [status(esa)], [d3_tarski])).
% 1.30/1.47  thf('48', plain,
% 1.30/1.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 1.30/1.47      inference('sup-', [status(thm)], ['46', '47'])).
% 1.30/1.47  thf('49', plain,
% 1.30/1.47      (![X0 : $i]:
% 1.30/1.47         (((sk_C_2) = (k3_xboole_0 @ X0 @ sk_C_2))
% 1.30/1.47          | (r2_hidden @ (sk_D @ sk_C_2 @ sk_C_2 @ X0) @ sk_B_1))),
% 1.30/1.47      inference('sup-', [status(thm)], ['26', '48'])).
% 1.30/1.47  thf('50', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]:
% 1.30/1.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.30/1.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.47      inference('eq_fact', [status(thm)], ['25'])).
% 1.30/1.47  thf('51', plain,
% 1.30/1.47      (![X8 : $i, X9 : $i, X12 : $i]:
% 1.30/1.47         (((X12) = (k3_xboole_0 @ X8 @ X9))
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X9)
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X8)
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X12 @ X9 @ X8) @ X12))),
% 1.30/1.47      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.30/1.47  thf('52', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]:
% 1.30/1.47         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.30/1.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.47      inference('sup-', [status(thm)], ['50', '51'])).
% 1.30/1.47  thf('53', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]:
% 1.30/1.47         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.30/1.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.47      inference('simplify', [status(thm)], ['52'])).
% 1.30/1.47  thf('54', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]:
% 1.30/1.47         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.30/1.47          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.30/1.47      inference('eq_fact', [status(thm)], ['25'])).
% 1.30/1.47  thf('55', plain,
% 1.30/1.47      (![X0 : $i, X1 : $i]:
% 1.30/1.47         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.30/1.47          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.30/1.47      inference('clc', [status(thm)], ['53', '54'])).
% 1.30/1.47  thf('56', plain,
% 1.30/1.47      ((((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 1.30/1.47        | ((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 1.30/1.47      inference('sup-', [status(thm)], ['49', '55'])).
% 1.30/1.47  thf('57', plain, (((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.30/1.47      inference('simplify', [status(thm)], ['56'])).
% 1.30/1.47  thf('58', plain, (((sk_C_2) = (sk_B_1))),
% 1.30/1.47      inference('sup+', [status(thm)], ['24', '57'])).
% 1.30/1.47  thf('59', plain, (((sk_B_1) != (sk_C_2))),
% 1.30/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.30/1.47  thf('60', plain, ($false),
% 1.30/1.47      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.30/1.47  
% 1.30/1.47  % SZS output end Refutation
% 1.30/1.47  
% 1.30/1.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
