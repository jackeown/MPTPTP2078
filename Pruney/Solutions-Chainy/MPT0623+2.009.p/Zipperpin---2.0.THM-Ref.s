%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tmgx9onin5

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 146 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   20
%              Number of atoms          :  537 (1179 expanded)
%              Number of equality atoms :   94 ( 218 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X10 @ X11 ) )
        = X11 )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X10 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X3 ) @ X5 )
      | ~ ( r2_hidden @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X10 @ X11 ) )
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

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

thf('6',plain,(
    ! [X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('11',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('12',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('13',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('14',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('16',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('17',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('18',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('25',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('26',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k6_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','23','26','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X10 @ X11 ) )
      | ( X11 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( v1_funct_1 @ X9 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('48',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('49',plain,(
    ! [X8: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X12 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('54',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('55',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('58',plain,(
    ! [X7: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','56','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['46','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tmgx9onin5
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 46 iterations in 0.019s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(t15_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.21/0.47       ( ![B:$i]:
% 0.21/0.47         ( ?[C:$i]:
% 0.21/0.47           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.21/0.47             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.47             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (((k1_relat_1 @ (sk_C @ X10 @ X11)) = (X11)) | ((X11) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         ((v1_funct_1 @ (sk_C @ X10 @ X11)) | ((X11) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.47  thf(t7_xboole_0, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.47          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.47  thf(l1_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X3 : $i, X5 : $i]:
% 0.21/0.47         ((r1_tarski @ (k1_tarski @ X3) @ X5) | ~ (r2_hidden @ X3 @ X5))),
% 0.21/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.47  thf('4', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         (((k2_relat_1 @ (sk_C @ X10 @ X11)) = (k1_tarski @ X10))
% 0.21/0.47          | ((X11) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.47  thf(t18_funct_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.47          ( ![C:$i]:
% 0.21/0.47            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.47                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.47             ( ![C:$i]:
% 0.21/0.47               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.47                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.47                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X12 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X12) @ sk_A)
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ X12))
% 0.21/0.47          | ~ (v1_funct_1 @ X12)
% 0.21/0.47          | ~ (v1_relat_1 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.21/0.47          | ((X1) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ (sk_C @ X0 @ X1))
% 0.21/0.47          | ~ (v1_funct_1 @ (sk_C @ X0 @ X1))
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ (sk_C @ X0 @ X1))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_A) = (k1_xboole_0))
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.21/0.47          | ~ (v1_funct_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.21/0.47          | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '7'])).
% 0.21/0.47  thf('9', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf(cc1_funct_1, axiom,
% 0.21/0.47    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.21/0.47  thf('11', plain, (![X9 : $i]: ((v1_funct_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.47  thf('13', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf('14', plain,
% 0.21/0.47      ((((k6_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.21/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((k6_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf(t71_relat_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.47       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.47  thf('17', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X12 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X12) @ sk_A)
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ X12))
% 0.21/0.47          | ~ (v1_funct_1 @ X12)
% 0.21/0.47          | ~ (v1_relat_1 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.21/0.47         | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.47         | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.47         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.21/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.47  thf('22', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.21/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      ((((k6_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.21/0.47  thf('25', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('26', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      ((((k6_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.47  thf('28', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('29', plain,
% 0.21/0.47      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.47  thf('30', plain,
% 0.21/0.47      (((~ (v1_funct_1 @ sk_B_1) | ((sk_B_1) != (sk_B_1))))
% 0.21/0.47         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('demod', [status(thm)], ['20', '23', '26', '29'])).
% 0.21/0.47  thf('31', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.21/0.47  thf('32', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['11', '31'])).
% 0.21/0.47  thf('33', plain,
% 0.21/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.47  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('35', plain,
% 0.21/0.47      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.21/0.47      inference('sup+', [status(thm)], ['33', '34'])).
% 0.21/0.47  thf('36', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['32', '35'])).
% 0.21/0.47  thf('37', plain,
% 0.21/0.47      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.21/0.47      inference('split', [status(esa)], ['9'])).
% 0.21/0.47  thf('38', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.21/0.47  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.47      inference('simpl_trail', [status(thm)], ['10', '38'])).
% 0.21/0.47  thf('40', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_B_1) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.21/0.47          | ~ (v1_funct_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.21/0.47          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.21/0.47          | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['8', '39'])).
% 0.21/0.47  thf('41', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0))
% 0.21/0.47          | ((X0) = (k1_xboole_0))
% 0.21/0.47          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '40'])).
% 0.21/0.47  thf('42', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_B_1) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.21/0.47          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.21/0.47          | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.47  thf('43', plain,
% 0.21/0.47      (![X10 : $i, X11 : $i]:
% 0.21/0.47         ((v1_relat_1 @ (sk_C @ X10 @ X11)) | ((X11) = (k1_xboole_0)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.21/0.47  thf('44', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((X0) = (k1_xboole_0))
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))))),
% 0.21/0.47      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.47  thf('45', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '44'])).
% 0.21/0.47  thf('46', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.47      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.47  thf('47', plain, (![X9 : $i]: ((v1_funct_1 @ X9) | ~ (v1_xboole_0 @ X9))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.21/0.47  thf('48', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf('49', plain, (![X8 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('50', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['48', '49'])).
% 0.21/0.47  thf('51', plain,
% 0.21/0.47      (![X12 : $i]:
% 0.21/0.47         (~ (r1_tarski @ (k2_relat_1 @ X12) @ sk_A)
% 0.21/0.47          | ((sk_B_1) != (k1_relat_1 @ X12))
% 0.21/0.47          | ~ (v1_funct_1 @ X12)
% 0.21/0.47          | ~ (v1_relat_1 @ X12))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('52', plain,
% 0.21/0.47      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.21/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.21/0.47        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['50', '51'])).
% 0.21/0.47  thf('53', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.21/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.47  thf('54', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf('55', plain, (![X6 : $i]: (v1_relat_1 @ (k6_relat_1 @ X6))),
% 0.21/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.21/0.47  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.47      inference('sup+', [status(thm)], ['54', '55'])).
% 0.21/0.47  thf('57', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.21/0.47  thf('58', plain, (![X7 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.21/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.47  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.47      inference('sup+', [status(thm)], ['57', '58'])).
% 0.21/0.47  thf('60', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['52', '53', '56', '59'])).
% 0.21/0.47  thf('61', plain,
% 0.21/0.47      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['47', '60'])).
% 0.21/0.47  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.47      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.47  thf('63', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.21/0.47      inference('demod', [status(thm)], ['61', '62'])).
% 0.21/0.47  thf('64', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['46', '63'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
