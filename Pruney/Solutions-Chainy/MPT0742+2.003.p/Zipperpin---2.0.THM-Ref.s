%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KgQKgtqyD1

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:51 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 184 expanded)
%              Number of leaves         :   22 (  66 expanded)
%              Depth                    :   21
%              Number of atoms          :  510 (1640 expanded)
%              Number of equality atoms :   27 (  74 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_ordinal1_type,type,(
    r1_ordinal1: $i > $i > $o )).

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

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ ( sk_C_1 @ X27 ) @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t32_ordinal1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ~ ( ( r1_tarski @ A @ B )
          & ( A != k1_xboole_0 )
          & ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ~ ( ( r2_hidden @ C @ A )
                  & ! [D: $i] :
                      ( ( v3_ordinal1 @ D )
                     => ( ( r2_hidden @ D @ A )
                       => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v3_ordinal1 @ B )
       => ~ ( ( r1_tarski @ A @ B )
            & ( A != k1_xboole_0 )
            & ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ~ ( ( r2_hidden @ C @ A )
                    & ! [D: $i] :
                        ( ( v3_ordinal1 @ D )
                       => ( ( r2_hidden @ D @ A )
                         => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_ordinal1])).

thf('3',plain,(
    ! [X33: $i] :
      ( ( r2_hidden @ ( sk_D @ X33 ) @ sk_A )
      | ~ ( r2_hidden @ X33 @ sk_A )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t23_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v3_ordinal1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( v3_ordinal1 @ A ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( v3_ordinal1 @ X29 )
      | ~ ( v3_ordinal1 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t23_ordinal1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ sk_B )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ ( sk_C_1 @ sk_A ) ) @ sk_A )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['4','13'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('15',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ( ( k2_xboole_0 @ sk_A @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ X0 )
        = ( k5_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ X0 ) )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['15','20'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('23',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,
    ( ( k1_xboole_0 = sk_A )
    | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf(t26_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r1_ordinal1 @ A @ B )
            | ( r2_hidden @ B @ A ) ) ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v3_ordinal1 @ X31 )
      | ( r1_ordinal1 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ X32 )
      | ~ ( v3_ordinal1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_ordinal1])).

thf('28',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( r2_hidden @ X28 @ ( sk_C_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( sk_C_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ ( sk_C_1 @ X0 ) )
      | ( r1_ordinal1 @ ( sk_C_1 @ X0 ) @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
      | ~ ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('34',plain,(
    ! [X33: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ X33 ) )
      | ~ ( r2_hidden @ X33 @ sk_A )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v3_ordinal1 @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_ordinal1 @ ( sk_C_1 @ sk_A ) @ ( sk_D @ ( sk_C_1 @ sk_A ) ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X33: $i] :
      ( ~ ( r1_ordinal1 @ X33 @ ( sk_D @ X33 ) )
      | ~ ( r2_hidden @ X33 @ sk_A )
      | ~ ( v3_ordinal1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v3_ordinal1 @ ( sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v3_ordinal1 @ ( sk_C_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ ( sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C_1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_xboole_0 @ X5 @ X4 )
        = X4 )
      | ~ ( r1_tarski @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_A @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( ( k3_xboole_0 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( k1_xboole_0
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ k1_xboole_0 )
      = X7 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    k1_xboole_0 = sk_A ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KgQKgtqyD1
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.38/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.63  % Solved by: fo/fo7.sh
% 0.38/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.63  % done 235 iterations in 0.179s
% 0.38/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.63  % SZS output start Refutation
% 0.38/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.63  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.63  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.38/0.63  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.38/0.63  thf(sk_D_type, type, sk_D: $i > $i).
% 0.38/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.63  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.63  thf(r1_ordinal1_type, type, r1_ordinal1: $i > $i > $o).
% 0.38/0.63  thf(d3_tarski, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_tarski @ A @ B ) <=>
% 0.38/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.38/0.63  thf('0', plain,
% 0.38/0.63      (![X1 : $i, X3 : $i]:
% 0.38/0.63         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.38/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.63  thf(t7_tarski, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ~( ( r2_hidden @ A @ B ) & 
% 0.38/0.63          ( ![C:$i]:
% 0.38/0.63            ( ~( ( r2_hidden @ C @ B ) & 
% 0.38/0.63                 ( ![D:$i]:
% 0.38/0.63                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.38/0.63  thf('1', plain,
% 0.38/0.63      (![X26 : $i, X27 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X26 @ X27) | (r2_hidden @ (sk_C_1 @ X27) @ X27))),
% 0.38/0.63      inference('cnf', [status(esa)], [t7_tarski])).
% 0.38/0.63  thf('2', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.63  thf(t32_ordinal1, conjecture,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( v3_ordinal1 @ B ) =>
% 0.38/0.63       ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.63            ( ![C:$i]:
% 0.38/0.63              ( ( v3_ordinal1 @ C ) =>
% 0.38/0.63                ( ~( ( r2_hidden @ C @ A ) & 
% 0.38/0.63                     ( ![D:$i]:
% 0.38/0.63                       ( ( v3_ordinal1 @ D ) =>
% 0.38/0.63                         ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 0.38/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.63    (~( ![A:$i,B:$i]:
% 0.38/0.63        ( ( v3_ordinal1 @ B ) =>
% 0.38/0.63          ( ~( ( r1_tarski @ A @ B ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.63               ( ![C:$i]:
% 0.38/0.63                 ( ( v3_ordinal1 @ C ) =>
% 0.38/0.63                   ( ~( ( r2_hidden @ C @ A ) & 
% 0.38/0.63                        ( ![D:$i]:
% 0.38/0.63                          ( ( v3_ordinal1 @ D ) =>
% 0.38/0.63                            ( ( r2_hidden @ D @ A ) => ( r1_ordinal1 @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 0.38/0.63    inference('cnf.neg', [status(esa)], [t32_ordinal1])).
% 0.38/0.63  thf('3', plain,
% 0.38/0.63      (![X33 : $i]:
% 0.38/0.63         ((r2_hidden @ (sk_D @ X33) @ sk_A)
% 0.38/0.63          | ~ (r2_hidden @ X33 @ sk_A)
% 0.38/0.63          | ~ (v3_ordinal1 @ X33))),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('4', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r1_tarski @ sk_A @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.38/0.63          | (r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['2', '3'])).
% 0.38/0.63  thf('5', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i]:
% 0.38/0.63         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.38/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.63  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('7', plain,
% 0.38/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.63         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.63          | (r2_hidden @ X0 @ X2)
% 0.38/0.63          | ~ (r1_tarski @ X1 @ X2))),
% 0.38/0.63      inference('cnf', [status(esa)], [d3_tarski])).
% 0.38/0.63  thf('8', plain,
% 0.38/0.63      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.38/0.63      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.63  thf('9', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C_1 @ sk_A) @ sk_B))),
% 0.38/0.63      inference('sup-', [status(thm)], ['5', '8'])).
% 0.38/0.63  thf(t23_ordinal1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( v3_ordinal1 @ B ) => ( ( r2_hidden @ A @ B ) => ( v3_ordinal1 @ A ) ) ))).
% 0.38/0.63  thf('10', plain,
% 0.38/0.63      (![X29 : $i, X30 : $i]:
% 0.38/0.63         ((v3_ordinal1 @ X29)
% 0.38/0.63          | ~ (v3_ordinal1 @ X30)
% 0.38/0.63          | ~ (r2_hidden @ X29 @ X30))),
% 0.38/0.63      inference('cnf', [status(esa)], [t23_ordinal1])).
% 0.38/0.63  thf('11', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r1_tarski @ sk_A @ X0)
% 0.38/0.63          | ~ (v3_ordinal1 @ sk_B)
% 0.38/0.63          | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.63  thf('12', plain, ((v3_ordinal1 @ sk_B)),
% 0.38/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.63  thf('13', plain,
% 0.38/0.63      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.63  thf('14', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((r2_hidden @ (sk_D @ (sk_C_1 @ sk_A)) @ sk_A)
% 0.38/0.63          | (r1_tarski @ sk_A @ X0))),
% 0.38/0.63      inference('clc', [status(thm)], ['4', '13'])).
% 0.38/0.63  thf(t5_boole, axiom,
% 0.38/0.63    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.38/0.63  thf('15', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.38/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.38/0.63  thf('16', plain,
% 0.38/0.63      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.38/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.38/0.63  thf(t12_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.63  thf('17', plain,
% 0.38/0.63      (![X4 : $i, X5 : $i]:
% 0.38/0.63         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.38/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.63  thf('18', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         ((v3_ordinal1 @ (sk_C_1 @ sk_A)) | ((k2_xboole_0 @ sk_A @ X0) = (X0)))),
% 0.38/0.63      inference('sup-', [status(thm)], ['16', '17'])).
% 0.38/0.63  thf(t95_xboole_1, axiom,
% 0.38/0.63    (![A:$i,B:$i]:
% 0.38/0.63     ( ( k3_xboole_0 @ A @ B ) =
% 0.38/0.63       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.38/0.63  thf('19', plain,
% 0.38/0.63      (![X8 : $i, X9 : $i]:
% 0.38/0.63         ((k3_xboole_0 @ X8 @ X9)
% 0.38/0.63           = (k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X9)))),
% 0.38/0.63      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.38/0.63  thf('20', plain,
% 0.38/0.63      (![X0 : $i]:
% 0.38/0.63         (((k3_xboole_0 @ sk_A @ X0)
% 0.38/0.63            = (k5_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ X0))
% 0.38/0.63          | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['18', '19'])).
% 0.47/0.63  thf('21', plain,
% 0.47/0.63      ((((k3_xboole_0 @ sk_A @ k1_xboole_0)
% 0.47/0.63          = (k5_xboole_0 @ sk_A @ k1_xboole_0))
% 0.47/0.63        | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['15', '20'])).
% 0.47/0.63  thf(t2_boole, axiom,
% 0.47/0.63    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.63  thf('22', plain,
% 0.47/0.63      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.63  thf('23', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.47/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.63  thf('24', plain,
% 0.47/0.63      ((((k1_xboole_0) = (sk_A)) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.47/0.63  thf('25', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('26', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.47/0.63      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.47/0.63  thf(t26_ordinal1, axiom,
% 0.47/0.63    (![A:$i]:
% 0.47/0.63     ( ( v3_ordinal1 @ A ) =>
% 0.47/0.63       ( ![B:$i]:
% 0.47/0.63         ( ( v3_ordinal1 @ B ) =>
% 0.47/0.63           ( ( r1_ordinal1 @ A @ B ) | ( r2_hidden @ B @ A ) ) ) ) ))).
% 0.47/0.63  thf('27', plain,
% 0.47/0.63      (![X31 : $i, X32 : $i]:
% 0.47/0.63         (~ (v3_ordinal1 @ X31)
% 0.47/0.63          | (r1_ordinal1 @ X32 @ X31)
% 0.47/0.63          | (r2_hidden @ X31 @ X32)
% 0.47/0.63          | ~ (v3_ordinal1 @ X32))),
% 0.47/0.63      inference('cnf', [status(esa)], [t26_ordinal1])).
% 0.47/0.63  thf('28', plain,
% 0.47/0.63      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X26 @ X27)
% 0.47/0.63          | ~ (r2_hidden @ X28 @ X27)
% 0.47/0.63          | ~ (r2_hidden @ X28 @ (sk_C_1 @ X27)))),
% 0.47/0.63      inference('cnf', [status(esa)], [t7_tarski])).
% 0.47/0.63  thf('29', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X1 @ (sk_C_1 @ X0)) | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.63      inference('condensation', [status(thm)], ['28'])).
% 0.47/0.63  thf('30', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         (~ (v3_ordinal1 @ (sk_C_1 @ X0))
% 0.47/0.63          | (r1_ordinal1 @ (sk_C_1 @ X0) @ X1)
% 0.47/0.63          | ~ (v3_ordinal1 @ X1)
% 0.47/0.63          | ~ (r2_hidden @ X1 @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['27', '29'])).
% 0.47/0.63  thf('31', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         (~ (r2_hidden @ X0 @ sk_A)
% 0.47/0.63          | ~ (v3_ordinal1 @ X0)
% 0.47/0.63          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['26', '30'])).
% 0.47/0.63  thf('32', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_A @ X0)
% 0.47/0.63          | (r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.47/0.63          | ~ (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['14', '31'])).
% 0.47/0.63  thf('33', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.63  thf('34', plain,
% 0.47/0.63      (![X33 : $i]:
% 0.47/0.63         ((v3_ordinal1 @ (sk_D @ X33))
% 0.47/0.63          | ~ (r2_hidden @ X33 @ sk_A)
% 0.47/0.63          | ~ (v3_ordinal1 @ X33))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('35', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_A @ X0)
% 0.47/0.63          | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.47/0.63          | (v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))))),
% 0.47/0.63      inference('sup-', [status(thm)], ['33', '34'])).
% 0.47/0.63  thf('36', plain,
% 0.47/0.63      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | (v3_ordinal1 @ (sk_C_1 @ sk_A)))),
% 0.47/0.63      inference('demod', [status(thm)], ['11', '12'])).
% 0.47/0.63  thf('37', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((v3_ordinal1 @ (sk_D @ (sk_C_1 @ sk_A))) | (r1_tarski @ sk_A @ X0))),
% 0.47/0.63      inference('clc', [status(thm)], ['35', '36'])).
% 0.47/0.63  thf('38', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_ordinal1 @ (sk_C_1 @ sk_A) @ (sk_D @ (sk_C_1 @ sk_A)))
% 0.47/0.63          | (r1_tarski @ sk_A @ X0))),
% 0.47/0.63      inference('clc', [status(thm)], ['32', '37'])).
% 0.47/0.63  thf('39', plain,
% 0.47/0.63      (![X33 : $i]:
% 0.47/0.63         (~ (r1_ordinal1 @ X33 @ (sk_D @ X33))
% 0.47/0.63          | ~ (r2_hidden @ X33 @ sk_A)
% 0.47/0.63          | ~ (v3_ordinal1 @ X33))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('40', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_A @ X0)
% 0.47/0.63          | ~ (v3_ordinal1 @ (sk_C_1 @ sk_A))
% 0.47/0.63          | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.47/0.63      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.63  thf('41', plain, ((v3_ordinal1 @ (sk_C_1 @ sk_A))),
% 0.47/0.63      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.47/0.63  thf('42', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ (sk_C_1 @ sk_A) @ sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['40', '41'])).
% 0.47/0.63  thf('43', plain,
% 0.47/0.63      (![X0 : $i, X1 : $i]:
% 0.47/0.63         ((r1_tarski @ X0 @ X1) | (r2_hidden @ (sk_C_1 @ X0) @ X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.63  thf('44', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.47/0.63      inference('clc', [status(thm)], ['42', '43'])).
% 0.47/0.63  thf('45', plain,
% 0.47/0.63      (![X4 : $i, X5 : $i]:
% 0.47/0.63         (((k2_xboole_0 @ X5 @ X4) = (X4)) | ~ (r1_tarski @ X5 @ X4))),
% 0.47/0.63      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.63  thf('46', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_A @ X0) = (X0))),
% 0.47/0.63      inference('sup-', [status(thm)], ['44', '45'])).
% 0.47/0.63  thf('47', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.47/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.63  thf('48', plain,
% 0.47/0.63      (![X8 : $i, X9 : $i]:
% 0.47/0.63         ((k3_xboole_0 @ X8 @ X9)
% 0.47/0.63           = (k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X9)))),
% 0.47/0.63      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.47/0.63  thf('49', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 0.47/0.63           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.47/0.63      inference('sup+', [status(thm)], ['47', '48'])).
% 0.47/0.63  thf('50', plain,
% 0.47/0.63      (![X6 : $i]: ((k3_xboole_0 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.63      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.63  thf('51', plain,
% 0.47/0.63      (![X0 : $i]:
% 0.47/0.63         ((k1_xboole_0) = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.47/0.63      inference('demod', [status(thm)], ['49', '50'])).
% 0.47/0.63  thf('52', plain, (((k1_xboole_0) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.47/0.63      inference('sup+', [status(thm)], ['46', '51'])).
% 0.47/0.63  thf('53', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ k1_xboole_0) = (X7))),
% 0.47/0.63      inference('cnf', [status(esa)], [t5_boole])).
% 0.47/0.63  thf('54', plain, (((k1_xboole_0) = (sk_A))),
% 0.47/0.63      inference('demod', [status(thm)], ['52', '53'])).
% 0.47/0.63  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.47/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.63  thf('56', plain, ($false),
% 0.47/0.63      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.47/0.63  
% 0.47/0.63  % SZS output end Refutation
% 0.47/0.63  
% 0.47/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
