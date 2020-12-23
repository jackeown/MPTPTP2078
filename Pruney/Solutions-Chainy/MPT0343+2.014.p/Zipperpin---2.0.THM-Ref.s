%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vy0CACeONS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:38 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 185 expanded)
%              Number of leaves         :   21 (  59 expanded)
%              Depth                    :   21
%              Number of atoms          :  492 (2142 expanded)
%              Number of equality atoms :   10 (  68 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X18: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( r1_tarski @ X21 @ X19 )
      | ( r2_hidden @ ( sk_D_2 @ X19 @ X21 @ X20 ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_C_2 @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( r1_tarski @ X21 @ X19 )
      | ( m1_subset_1 @ ( sk_D_2 @ X19 @ X21 @ X20 ) @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ sk_C_2 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_C_2 )
      | ( r2_hidden @ X22 @ sk_B )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_C_2 @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_C_2 @ sk_A ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_C_2 @ sk_A ) @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_B @ sk_C_2 @ sk_A ) @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( r1_tarski @ X21 @ X19 )
      | ~ ( r2_hidden @ ( sk_D_2 @ X19 @ X21 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(simplify,[status(thm)],['24'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('27',plain,
    ( ( sk_C_2 = sk_B )
    | ( r2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_xboole_0 @ sk_C_2 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('31',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ( r2_hidden @ X9 @ X10 )
      | ( X10
       != ( k3_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X9 @ ( k3_tarski @ X8 ) )
      | ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('36',plain,(
    ! [X14: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('37',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( m1_subset_1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ X15 @ X16 )
      | ~ ( r2_hidden @ X15 @ X16 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_B )
      | ( r2_hidden @ X22 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X22 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf('45',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_C_2 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('47',plain,(
    ~ ( r2_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r2_xboole_0 @ sk_C_2 @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vy0CACeONS
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:37:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.56/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.73  % Solved by: fo/fo7.sh
% 0.56/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.73  % done 295 iterations in 0.280s
% 0.56/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.73  % SZS output start Refutation
% 0.56/0.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.56/0.73  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.56/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.56/0.73  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.56/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.73  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.56/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.56/0.73  thf(t8_subset_1, conjecture,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73       ( ![C:$i]:
% 0.56/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73           ( ( ![D:$i]:
% 0.56/0.73               ( ( m1_subset_1 @ D @ A ) =>
% 0.56/0.73                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.56/0.73             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.56/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.73    (~( ![A:$i,B:$i]:
% 0.56/0.73        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73          ( ![C:$i]:
% 0.56/0.73            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73              ( ( ![D:$i]:
% 0.56/0.73                  ( ( m1_subset_1 @ D @ A ) =>
% 0.56/0.73                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.56/0.73                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.56/0.73    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.56/0.73  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(d2_subset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( ( v1_xboole_0 @ A ) =>
% 0.56/0.73         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.56/0.73       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.56/0.73         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.73  thf('1', plain,
% 0.56/0.73      (![X15 : $i, X16 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X15 @ X16)
% 0.56/0.73          | (r2_hidden @ X15 @ X16)
% 0.56/0.73          | (v1_xboole_0 @ X16))),
% 0.56/0.73      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.56/0.73  thf('2', plain,
% 0.56/0.73      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.73        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.56/0.73  thf(fc1_subset_1, axiom,
% 0.56/0.73    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.56/0.73  thf('3', plain, (![X18 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.56/0.73      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.56/0.73  thf('4', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('clc', [status(thm)], ['2', '3'])).
% 0.56/0.73  thf('5', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf(t7_subset_1, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73       ( ![C:$i]:
% 0.56/0.73         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.73           ( ( ![D:$i]:
% 0.56/0.73               ( ( m1_subset_1 @ D @ A ) =>
% 0.56/0.73                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.56/0.73             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.56/0.73  thf('7', plain,
% 0.56/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.56/0.73          | (r1_tarski @ X21 @ X19)
% 0.56/0.73          | (r2_hidden @ (sk_D_2 @ X19 @ X21 @ X20) @ X21)
% 0.56/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.56/0.73  thf('8', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.73          | (r2_hidden @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ X0)
% 0.56/0.73          | (r1_tarski @ X0 @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['6', '7'])).
% 0.56/0.73  thf('9', plain,
% 0.56/0.73      (((r1_tarski @ sk_C_2 @ sk_B)
% 0.56/0.73        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_C_2 @ sk_A) @ sk_C_2))),
% 0.56/0.73      inference('sup-', [status(thm)], ['5', '8'])).
% 0.56/0.73  thf('10', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('11', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('12', plain,
% 0.56/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.56/0.73          | (r1_tarski @ X21 @ X19)
% 0.56/0.73          | (m1_subset_1 @ (sk_D_2 @ X19 @ X21 @ X20) @ X20)
% 0.56/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.56/0.73  thf('13', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.73          | (m1_subset_1 @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.56/0.73          | (r1_tarski @ X0 @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['11', '12'])).
% 0.56/0.73  thf('14', plain,
% 0.56/0.73      (((r1_tarski @ sk_C_2 @ sk_B)
% 0.56/0.73        | (m1_subset_1 @ (sk_D_2 @ sk_B @ sk_C_2 @ sk_A) @ sk_A))),
% 0.56/0.73      inference('sup-', [status(thm)], ['10', '13'])).
% 0.56/0.73  thf('15', plain,
% 0.56/0.73      (![X22 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X22 @ sk_C_2)
% 0.56/0.73          | (r2_hidden @ X22 @ sk_B)
% 0.56/0.73          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('16', plain,
% 0.56/0.73      (((r1_tarski @ sk_C_2 @ sk_B)
% 0.56/0.73        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_C_2 @ sk_A) @ sk_B)
% 0.56/0.73        | ~ (r2_hidden @ (sk_D_2 @ sk_B @ sk_C_2 @ sk_A) @ sk_C_2))),
% 0.56/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.56/0.73  thf('17', plain,
% 0.56/0.73      (((r1_tarski @ sk_C_2 @ sk_B)
% 0.56/0.73        | (r2_hidden @ (sk_D_2 @ sk_B @ sk_C_2 @ sk_A) @ sk_B)
% 0.56/0.73        | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['9', '16'])).
% 0.56/0.73  thf('18', plain,
% 0.56/0.73      (((r2_hidden @ (sk_D_2 @ sk_B @ sk_C_2 @ sk_A) @ sk_B)
% 0.56/0.73        | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.56/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.56/0.73  thf('19', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('20', plain,
% 0.56/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.56/0.73          | (r1_tarski @ X21 @ X19)
% 0.56/0.73          | ~ (r2_hidden @ (sk_D_2 @ X19 @ X21 @ X20) @ X19)
% 0.56/0.73          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.56/0.73      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.56/0.73  thf('21', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.56/0.73          | ~ (r2_hidden @ (sk_D_2 @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.56/0.73          | (r1_tarski @ X0 @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.56/0.73  thf('22', plain,
% 0.56/0.73      (((r1_tarski @ sk_C_2 @ sk_B)
% 0.56/0.73        | (r1_tarski @ sk_C_2 @ sk_B)
% 0.56/0.73        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['18', '21'])).
% 0.56/0.73  thf('23', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('24', plain,
% 0.56/0.73      (((r1_tarski @ sk_C_2 @ sk_B) | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.56/0.73      inference('demod', [status(thm)], ['22', '23'])).
% 0.56/0.73  thf('25', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 0.56/0.73      inference('simplify', [status(thm)], ['24'])).
% 0.56/0.73  thf(d8_xboole_0, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.56/0.73       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.56/0.73  thf('26', plain,
% 0.56/0.73      (![X0 : $i, X2 : $i]:
% 0.56/0.73         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.56/0.73      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.56/0.73  thf('27', plain, ((((sk_C_2) = (sk_B)) | (r2_xboole_0 @ sk_C_2 @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.56/0.73  thf('28', plain, (((sk_B) != (sk_C_2))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('29', plain, ((r2_xboole_0 @ sk_C_2 @ sk_B)),
% 0.56/0.73      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.56/0.73  thf(t6_xboole_0, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.56/0.73          ( ![C:$i]:
% 0.56/0.73            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.56/0.73  thf('30', plain,
% 0.56/0.73      (![X3 : $i, X4 : $i]:
% 0.56/0.73         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.56/0.73      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.56/0.73  thf('31', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ sk_B)),
% 0.56/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.73  thf(d4_tarski, axiom,
% 0.56/0.73    (![A:$i,B:$i]:
% 0.56/0.73     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.56/0.73       ( ![C:$i]:
% 0.56/0.73         ( ( r2_hidden @ C @ B ) <=>
% 0.56/0.73           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.56/0.73  thf('32', plain,
% 0.56/0.73      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X7 @ X8)
% 0.56/0.73          | ~ (r2_hidden @ X9 @ X7)
% 0.56/0.73          | (r2_hidden @ X9 @ X10)
% 0.56/0.73          | ((X10) != (k3_tarski @ X8)))),
% 0.56/0.73      inference('cnf', [status(esa)], [d4_tarski])).
% 0.56/0.73  thf('33', plain,
% 0.56/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.56/0.73         ((r2_hidden @ X9 @ (k3_tarski @ X8))
% 0.56/0.73          | ~ (r2_hidden @ X9 @ X7)
% 0.56/0.73          | ~ (r2_hidden @ X7 @ X8))),
% 0.56/0.73      inference('simplify', [status(thm)], ['32'])).
% 0.56/0.73  thf('34', plain,
% 0.56/0.73      (![X0 : $i]:
% 0.56/0.73         (~ (r2_hidden @ sk_B @ X0)
% 0.56/0.73          | (r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ (k3_tarski @ X0)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['31', '33'])).
% 0.56/0.73  thf('35', plain,
% 0.56/0.73      ((r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ (k3_tarski @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.73      inference('sup-', [status(thm)], ['4', '34'])).
% 0.56/0.73  thf(t99_zfmisc_1, axiom,
% 0.56/0.73    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.56/0.73  thf('36', plain, (![X14 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X14)) = (X14))),
% 0.56/0.73      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.56/0.73  thf('37', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ sk_A)),
% 0.56/0.73      inference('demod', [status(thm)], ['35', '36'])).
% 0.56/0.73  thf('38', plain,
% 0.56/0.73      (![X15 : $i, X16 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X15 @ X16)
% 0.56/0.73          | (m1_subset_1 @ X15 @ X16)
% 0.56/0.73          | (v1_xboole_0 @ X16))),
% 0.56/0.73      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.56/0.73  thf(t7_boole, axiom,
% 0.56/0.73    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( v1_xboole_0 @ B ) ) ))).
% 0.56/0.73  thf('39', plain,
% 0.56/0.73      (![X5 : $i, X6 : $i]: (~ (r2_hidden @ X5 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.56/0.73      inference('cnf', [status(esa)], [t7_boole])).
% 0.56/0.73  thf('40', plain,
% 0.56/0.73      (![X15 : $i, X16 : $i]:
% 0.56/0.73         ((m1_subset_1 @ X15 @ X16) | ~ (r2_hidden @ X15 @ X16))),
% 0.56/0.73      inference('clc', [status(thm)], ['38', '39'])).
% 0.56/0.73  thf('41', plain, ((m1_subset_1 @ (sk_C @ sk_B @ sk_C_2) @ sk_A)),
% 0.56/0.73      inference('sup-', [status(thm)], ['37', '40'])).
% 0.56/0.73  thf('42', plain,
% 0.56/0.73      (![X22 : $i]:
% 0.56/0.73         (~ (r2_hidden @ X22 @ sk_B)
% 0.56/0.73          | (r2_hidden @ X22 @ sk_C_2)
% 0.56/0.73          | ~ (m1_subset_1 @ X22 @ sk_A))),
% 0.56/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.73  thf('43', plain,
% 0.56/0.73      (((r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ sk_C_2)
% 0.56/0.73        | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ sk_B))),
% 0.56/0.73      inference('sup-', [status(thm)], ['41', '42'])).
% 0.56/0.73  thf('44', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ sk_B)),
% 0.56/0.73      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.73  thf('45', plain, ((r2_hidden @ (sk_C @ sk_B @ sk_C_2) @ sk_C_2)),
% 0.56/0.73      inference('demod', [status(thm)], ['43', '44'])).
% 0.56/0.73  thf('46', plain,
% 0.56/0.73      (![X3 : $i, X4 : $i]:
% 0.56/0.73         (~ (r2_xboole_0 @ X3 @ X4) | ~ (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.56/0.73      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.56/0.73  thf('47', plain, (~ (r2_xboole_0 @ sk_C_2 @ sk_B)),
% 0.56/0.73      inference('sup-', [status(thm)], ['45', '46'])).
% 0.56/0.73  thf('48', plain, ((r2_xboole_0 @ sk_C_2 @ sk_B)),
% 0.56/0.73      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.56/0.73  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.56/0.73  
% 0.56/0.73  % SZS output end Refutation
% 0.56/0.73  
% 0.56/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
