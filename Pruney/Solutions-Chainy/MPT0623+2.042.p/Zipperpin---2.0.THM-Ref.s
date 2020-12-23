%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIpcLlklui

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:41 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 118 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  555 (1043 expanded)
%              Number of equality atoms :   78 ( 152 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(np__1_type,type,(
    np__1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X22: $i,X23: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X22 @ X23 ) )
        = X23 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X22 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('5',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('10',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('11',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X22 @ X23 ) )
        = ( k1_tarski @ X22 ) )
      | ( X23 = k1_xboole_0 ) ) ),
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

thf('18',plain,(
    ! [X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('24',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_B @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( sk_B @ k1_xboole_0 ) )
    | ( sk_B_1
     != ( k1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('33',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('34',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('36',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','36'])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['21'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['22','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X22 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ k1_xboole_0 @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIpcLlklui
% 0.12/0.32  % Computer   : n013.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:04:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.49  % Solved by: fo/fo7.sh
% 0.18/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.49  % done 77 iterations in 0.056s
% 0.18/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.49  % SZS output start Refutation
% 0.18/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.18/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.49  thf(np__1_type, type, np__1: $i).
% 0.18/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.18/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.18/0.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.18/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.18/0.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.18/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.18/0.49  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.18/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.49  thf(t15_funct_1, axiom,
% 0.18/0.49    (![A:$i]:
% 0.18/0.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.18/0.49       ( ![B:$i]:
% 0.18/0.49         ( ?[C:$i]:
% 0.18/0.49           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.18/0.49             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.18/0.49             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.18/0.49  thf('0', plain,
% 0.18/0.49      (![X22 : $i, X23 : $i]:
% 0.18/0.49         (((k1_relat_1 @ (sk_C_3 @ X22 @ X23)) = (X23))
% 0.18/0.49          | ((X23) = (k1_xboole_0)))),
% 0.18/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.18/0.49  thf('1', plain,
% 0.18/0.49      (![X22 : $i, X23 : $i]:
% 0.18/0.49         ((v1_funct_1 @ (sk_C_3 @ X22 @ X23)) | ((X23) = (k1_xboole_0)))),
% 0.18/0.49      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.18/0.49  thf(t2_tarski, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.18/0.49       ( ( A ) = ( B ) ) ))).
% 0.18/0.49  thf('2', plain,
% 0.18/0.49      (![X10 : $i, X11 : $i]:
% 0.18/0.49         (((X11) = (X10))
% 0.18/0.49          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X10)
% 0.18/0.49          | (r2_hidden @ (sk_C_1 @ X10 @ X11) @ X11))),
% 0.18/0.49      inference('cnf', [status(esa)], [t2_tarski])).
% 0.18/0.49  thf(t3_boole, axiom,
% 0.18/0.49    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.18/0.49  thf('3', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.18/0.49      inference('cnf', [status(esa)], [t3_boole])).
% 0.18/0.49  thf(d5_xboole_0, axiom,
% 0.18/0.49    (![A:$i,B:$i,C:$i]:
% 0.18/0.49     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.18/0.49       ( ![D:$i]:
% 0.18/0.49         ( ( r2_hidden @ D @ C ) <=>
% 0.18/0.49           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.18/0.49  thf('4', plain,
% 0.18/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X8 @ X7)
% 0.18/0.49          | ~ (r2_hidden @ X8 @ X6)
% 0.18/0.49          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.18/0.49      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.18/0.49  thf('5', plain,
% 0.18/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X8 @ X6)
% 0.18/0.49          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['4'])).
% 0.18/0.49  thf('6', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['3', '5'])).
% 0.18/0.49  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.18/0.49      inference('condensation', [status(thm)], ['6'])).
% 0.18/0.49  thf('8', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.18/0.49          | ((X0) = (k1_xboole_0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['2', '7'])).
% 0.18/0.49  thf(d3_tarski, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.18/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.18/0.49  thf('9', plain,
% 0.18/0.49      (![X1 : $i, X3 : $i]:
% 0.18/0.49         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.49  thf(d1_tarski, axiom,
% 0.18/0.49    (![A:$i,B:$i]:
% 0.18/0.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.18/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.18/0.49  thf('10', plain,
% 0.18/0.49      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X17 @ X16)
% 0.18/0.49          | ((X17) = (X14))
% 0.18/0.49          | ((X16) != (k1_tarski @ X14)))),
% 0.18/0.49      inference('cnf', [status(esa)], [d1_tarski])).
% 0.18/0.49  thf('11', plain,
% 0.18/0.49      (![X14 : $i, X17 : $i]:
% 0.18/0.49         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.18/0.49      inference('simplify', [status(thm)], ['10'])).
% 0.18/0.49  thf('12', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.18/0.49          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.18/0.49      inference('sup-', [status(thm)], ['9', '11'])).
% 0.18/0.49  thf('13', plain,
% 0.18/0.49      (![X1 : $i, X3 : $i]:
% 0.18/0.49         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.18/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.49  thf('14', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.49          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.18/0.49          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.18/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.18/0.49  thf('15', plain,
% 0.18/0.49      (![X0 : $i, X1 : $i]:
% 0.18/0.49         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.18/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.18/0.49  thf('16', plain,
% 0.18/0.49      (![X0 : $i]:
% 0.18/0.49         (((X0) = (k1_xboole_0))
% 0.18/0.49          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0)) @ X0))),
% 0.18/0.49      inference('sup-', [status(thm)], ['8', '15'])).
% 0.18/0.50  thf('17', plain,
% 0.18/0.50      (![X22 : $i, X23 : $i]:
% 0.18/0.50         (((k2_relat_1 @ (sk_C_3 @ X22 @ X23)) = (k1_tarski @ X22))
% 0.18/0.50          | ((X23) = (k1_xboole_0)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.18/0.50  thf(t18_funct_1, conjecture,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.18/0.50          ( ![C:$i]:
% 0.18/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.50              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.18/0.50                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.18/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.50    (~( ![A:$i,B:$i]:
% 0.18/0.50        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.18/0.50             ( ![C:$i]:
% 0.18/0.50               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.18/0.50                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.18/0.50                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.18/0.50    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.18/0.50  thf('18', plain,
% 0.18/0.50      (![X24 : $i]:
% 0.18/0.50         (~ (r1_tarski @ (k2_relat_1 @ X24) @ sk_A)
% 0.18/0.50          | ((sk_B_1) != (k1_relat_1 @ X24))
% 0.18/0.50          | ~ (v1_funct_1 @ X24)
% 0.18/0.50          | ~ (v1_relat_1 @ X24))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('19', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.18/0.50          | ((X1) = (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.18/0.50          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.18/0.50          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.18/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.18/0.50  thf('20', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((sk_A) = (k1_xboole_0))
% 0.18/0.50          | ((sk_B_1)
% 0.18/0.50              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)))
% 0.18/0.50          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.18/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.18/0.50          | ((X0) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.18/0.50  thf('21', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('22', plain,
% 0.18/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.18/0.50      inference('split', [status(esa)], ['21'])).
% 0.18/0.50  thf('23', plain,
% 0.18/0.50      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.18/0.50      inference('split', [status(esa)], ['21'])).
% 0.18/0.50  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ?[B:$i]:
% 0.18/0.50       ( ( ![C:$i]:
% 0.18/0.50           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.18/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.18/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.18/0.50  thf('24', plain, (![X20 : $i]: ((k1_relat_1 @ (sk_B @ X20)) = (X20))),
% 0.18/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.18/0.50  thf(t65_relat_1, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( v1_relat_1 @ A ) =>
% 0.18/0.50       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.18/0.50         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.18/0.50  thf('25', plain,
% 0.18/0.50      (![X19 : $i]:
% 0.18/0.50         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.18/0.50          | ((k2_relat_1 @ X19) = (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ X19))),
% 0.18/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.18/0.50  thf('26', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((X0) != (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.18/0.50          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.18/0.50  thf('27', plain, (![X20 : $i]: (v1_relat_1 @ (sk_B @ X20))),
% 0.18/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.18/0.50  thf('28', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((X0) != (k1_xboole_0))
% 0.18/0.50          | ((k2_relat_1 @ (sk_B @ X0)) = (k1_xboole_0)))),
% 0.18/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.18/0.50  thf('29', plain, (((k2_relat_1 @ (sk_B @ k1_xboole_0)) = (k1_xboole_0))),
% 0.18/0.50      inference('simplify', [status(thm)], ['28'])).
% 0.18/0.50  thf('30', plain,
% 0.18/0.50      (![X24 : $i]:
% 0.18/0.50         (~ (r1_tarski @ (k2_relat_1 @ X24) @ sk_A)
% 0.18/0.50          | ((sk_B_1) != (k1_relat_1 @ X24))
% 0.18/0.50          | ~ (v1_funct_1 @ X24)
% 0.18/0.50          | ~ (v1_relat_1 @ X24))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('31', plain,
% 0.18/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.18/0.50        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0))
% 0.18/0.50        | ~ (v1_funct_1 @ (sk_B @ k1_xboole_0))
% 0.18/0.50        | ((sk_B_1) != (k1_relat_1 @ (sk_B @ k1_xboole_0))))),
% 0.18/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.18/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.50  thf('32', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.18/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.50  thf('33', plain, (![X20 : $i]: (v1_relat_1 @ (sk_B @ X20))),
% 0.18/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.18/0.50  thf('34', plain, (![X20 : $i]: (v1_funct_1 @ (sk_B @ X20))),
% 0.18/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.18/0.50  thf('35', plain, (![X20 : $i]: ((k1_relat_1 @ (sk_B @ X20)) = (X20))),
% 0.18/0.50      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.18/0.50  thf('36', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.18/0.50      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.18/0.50  thf('37', plain,
% 0.18/0.50      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.18/0.50      inference('sup-', [status(thm)], ['23', '36'])).
% 0.18/0.50  thf('38', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.18/0.50  thf('39', plain,
% 0.18/0.50      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.18/0.50      inference('split', [status(esa)], ['21'])).
% 0.18/0.50  thf('40', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.18/0.50      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.18/0.50  thf('41', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.50      inference('simpl_trail', [status(thm)], ['22', '40'])).
% 0.18/0.50  thf('42', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((sk_B_1)
% 0.18/0.50            != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)))
% 0.18/0.50          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.18/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.18/0.50          | ((X0) = (k1_xboole_0)))),
% 0.18/0.50      inference('simplify_reflect-', [status(thm)], ['20', '41'])).
% 0.18/0.50  thf('43', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((X0) = (k1_xboole_0))
% 0.18/0.50          | ((X0) = (k1_xboole_0))
% 0.18/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.18/0.50          | ((sk_B_1)
% 0.18/0.50              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))))),
% 0.18/0.50      inference('sup-', [status(thm)], ['1', '42'])).
% 0.18/0.50  thf('44', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((sk_B_1)
% 0.18/0.50            != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0)))
% 0.18/0.50          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))
% 0.18/0.50          | ((X0) = (k1_xboole_0)))),
% 0.18/0.50      inference('simplify', [status(thm)], ['43'])).
% 0.18/0.50  thf('45', plain,
% 0.18/0.50      (![X22 : $i, X23 : $i]:
% 0.18/0.50         ((v1_relat_1 @ (sk_C_3 @ X22 @ X23)) | ((X23) = (k1_xboole_0)))),
% 0.18/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.18/0.50  thf('46', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((X0) = (k1_xboole_0))
% 0.18/0.50          | ((sk_B_1)
% 0.18/0.50              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ k1_xboole_0 @ sk_A) @ X0))))),
% 0.18/0.50      inference('clc', [status(thm)], ['44', '45'])).
% 0.18/0.50  thf('47', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['0', '46'])).
% 0.18/0.50  thf('48', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.18/0.50      inference('simplify', [status(thm)], ['47'])).
% 0.18/0.50  thf('49', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.18/0.50      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.18/0.50  thf('50', plain, ($false),
% 0.18/0.50      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.18/0.50  
% 0.18/0.50  % SZS output end Refutation
% 0.18/0.50  
% 0.18/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
