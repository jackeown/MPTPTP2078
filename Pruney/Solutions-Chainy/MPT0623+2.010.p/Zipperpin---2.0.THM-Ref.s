%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pn18g3LKmJ

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 136 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :   14
%              Number of atoms          :  532 (1020 expanded)
%              Number of equality atoms :   79 ( 158 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X11 ) @ ( sk_C @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('9',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('17',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_2 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('22',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('23',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( X16 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('29',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','29'])).

thf('31',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','30'])).

thf('32',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_1 @ X21 @ X22 ) )
        = X22 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('39',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_relat_1 @ ( sk_C_1 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('40',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_funct_1 @ ( sk_C_1 @ X21 @ X22 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('41',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('42',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X5 ) @ X7 )
      | ~ ( r2_hidden @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_1 @ X21 @ X22 ) )
        = ( k1_tarski @ X21 ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('45',plain,(
    ! [X23: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X23 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','29'])).

thf('55',plain,(
    v1_xboole_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['37','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Pn18g3LKmJ
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:47:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 70 iterations in 0.039s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(t60_relat_1, axiom,
% 0.20/0.49    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.49     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('0', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.49  thf(d5_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X11 : $i, X14 : $i]:
% 0.20/0.49         (((X14) = (k2_relat_1 @ X11))
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (k4_tarski @ (sk_D @ X14 @ X11) @ (sk_C @ X14 @ X11)) @ X11)
% 0.20/0.49          | (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.20/0.49          | ((X1) = (k2_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X1)
% 0.20/0.49          | ((X0) = (k2_relat_1 @ X1))
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_xboole_0 @ X0)
% 0.20/0.49          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '5'])).
% 0.20/0.49  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.49  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf(t18_funct_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49          ( ![C:$i]:
% 0.20/0.49            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.49                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i]:
% 0.20/0.49        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49             ( ![C:$i]:
% 0.20/0.49               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.20/0.49                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.20/0.49  thf('9', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.20/0.49      inference('split', [status(esa)], ['9'])).
% 0.20/0.49  thf(cc1_relat_1, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.49  thf('12', plain, (![X8 : $i]: ((v1_relat_1 @ X8) | ~ (v1_xboole_0 @ X8))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.49  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.20/0.49        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.49        | ((sk_B_2) != (k1_relat_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.49  thf('16', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.49  thf('17', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.49        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.20/0.49        | ((sk_B_2) != (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49        | ((sk_B_2) != (k1_xboole_0))
% 0.20/0.49        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '18'])).
% 0.20/0.49  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      ((((sk_B_2) != (k1_xboole_0)) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ?[B:$i]:
% 0.20/0.49       ( ( ![C:$i]:
% 0.20/0.49           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.49             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.49         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.49         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.49  thf('22', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B_1 @ X17)) = (X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf(t64_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.20/0.49          | ((X16) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.20/0.49          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.49  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.49  thf('28', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B_1 @ X17))),
% 0.20/0.49      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.49  thf('29', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.49  thf('30', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '29'])).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      ((((sk_B_2) != (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['11', '30'])).
% 0.20/0.49  thf('32', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.49      inference('split', [status(esa)], ['9'])).
% 0.20/0.49  thf('34', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['10', '34'])).
% 0.20/0.49  thf('36', plain, (![X0 : $i]: (((sk_A) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '35'])).
% 0.20/0.49  thf('37', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  thf(t15_funct_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ?[C:$i]:
% 0.20/0.49           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.20/0.49             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.49             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         (((k1_relat_1 @ (sk_C_1 @ X21 @ X22)) = (X22))
% 0.20/0.49          | ((X22) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         ((v1_relat_1 @ (sk_C_1 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.49  thf('40', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         ((v1_funct_1 @ (sk_C_1 @ X21 @ X22)) | ((X22) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.49  thf('41', plain,
% 0.20/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf(l1_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X5 : $i, X7 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_tarski @ X5) @ X7) | ~ (r2_hidden @ X5 @ X7))),
% 0.20/0.49      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         (((k2_relat_1 @ (sk_C_1 @ X21 @ X22)) = (k1_tarski @ X21))
% 0.20/0.49          | ((X22) = (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.20/0.49  thf('45', plain,
% 0.20/0.49      (![X23 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k2_relat_1 @ X23) @ sk_A)
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ X23))
% 0.20/0.49          | ~ (v1_funct_1 @ X23)
% 0.20/0.49          | ~ (v1_relat_1 @ X23))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('46', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.20/0.49          | ((X1) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ X1))
% 0.20/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ X0 @ X1))
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ (sk_C_1 @ X0 @ X1))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.49  thf('47', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.49          | ~ (v1_funct_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['43', '46'])).
% 0.20/0.49  thf('48', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['40', '47'])).
% 0.20/0.49  thf('49', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.49  thf('50', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['39', '49'])).
% 0.20/0.49  thf('51', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ sk_A)
% 0.20/0.49          | ((sk_B_2) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.20/0.49          | ((X0) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.49  thf('52', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_B_2) != (X0))
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | ((X0) = (k1_xboole_0))
% 0.20/0.49          | (v1_xboole_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['38', '51'])).
% 0.20/0.49  thf('53', plain, (((v1_xboole_0 @ sk_A) | ((sk_B_2) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['52'])).
% 0.20/0.49  thf('54', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '29'])).
% 0.20/0.49  thf('55', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.20/0.49  thf('56', plain, ($false),
% 0.20/0.49      inference('simplify_reflect+', [status(thm)], ['37', '55'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
