%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TkBaLLsJxf

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 146 expanded)
%              Number of leaves         :   30 (  57 expanded)
%              Depth                    :   18
%              Number of atoms          :  534 (1190 expanded)
%              Number of equality atoms :   79 ( 190 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

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
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X22 @ X23 ) )
        = X23 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_funct_1 @ ( sk_C_2 @ X22 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X17 @ X14 ) @ ( sk_D @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('7',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X7 ) @ X9 )
      | ~ ( r2_hidden @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_1 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X22 @ X23 ) )
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

thf('14',plain,(
    ! [X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('20',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('21',plain,(
    ! [X24: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X24 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('23',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('24',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23','24'])).

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

thf('26',plain,(
    ! [X20: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X20 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('27',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('33',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','33'])).

thf('35',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('36',plain,(
    ! [X20: $i] :
      ( v1_funct_1 @ ( sk_B @ X20 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('37',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','38'])).

thf('40',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['17'])).

thf('42',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X22 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['34','37'])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TkBaLLsJxf
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:46:20 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 76 iterations in 0.034s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.47  thf(np__1_type, type, np__1: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.19/0.47  thf(t15_funct_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ?[C:$i]:
% 0.19/0.47           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.19/0.47             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.47             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.47  thf('0', plain,
% 0.19/0.47      (![X22 : $i, X23 : $i]:
% 0.19/0.47         (((k1_relat_1 @ (sk_C_2 @ X22 @ X23)) = (X23))
% 0.19/0.47          | ((X23) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X22 : $i, X23 : $i]:
% 0.19/0.47         ((v1_funct_1 @ (sk_C_2 @ X22 @ X23)) | ((X23) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.47  thf(d4_relat_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.47       ( ![C:$i]:
% 0.19/0.47         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.47           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X14 : $i, X17 : $i]:
% 0.19/0.47         (((X17) = (k1_relat_1 @ X14))
% 0.19/0.47          | (r2_hidden @ 
% 0.19/0.47             (k4_tarski @ (sk_C_1 @ X17 @ X14) @ (sk_D @ X17 @ X14)) @ X14)
% 0.19/0.47          | (r2_hidden @ (sk_C_1 @ X17 @ X14) @ X17))),
% 0.19/0.47      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.47  thf(t2_boole, axiom,
% 0.19/0.47    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.47  thf(t4_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.19/0.47          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.47  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.47  thf('6', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.19/0.47      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.47  thf('7', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.19/0.47      inference('demod', [status(thm)], ['5', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.47          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '7'])).
% 0.19/0.47  thf(t60_relat_1, axiom,
% 0.19/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.47  thf('9', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.19/0.47          | ((X0) = (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf(l1_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X7 : $i, X9 : $i]:
% 0.19/0.47         ((r1_tarski @ (k1_tarski @ X7) @ X9) | ~ (r2_hidden @ X7 @ X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((X0) = (k1_xboole_0))
% 0.19/0.47          | (r1_tarski @ (k1_tarski @ (sk_C_1 @ X0 @ k1_xboole_0)) @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X22 : $i, X23 : $i]:
% 0.19/0.47         (((k2_relat_1 @ (sk_C_2 @ X22 @ X23)) = (k1_tarski @ X22))
% 0.19/0.47          | ((X23) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.47  thf(t18_funct_1, conjecture,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.47          ( ![C:$i]:
% 0.19/0.47            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.47              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.47                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i]:
% 0.19/0.47        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.47             ( ![C:$i]:
% 0.19/0.47               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.47                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.47                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X24 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k2_relat_1 @ X24) @ sk_A)
% 0.19/0.47          | ((sk_B_1) != (k1_relat_1 @ X24))
% 0.19/0.47          | ~ (v1_funct_1 @ X24)
% 0.19/0.47          | ~ (v1_relat_1 @ X24))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.19/0.47          | ((X1) = (k1_xboole_0))
% 0.19/0.47          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.19/0.47          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.19/0.47          | ((sk_B_1) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((sk_A) = (k1_xboole_0))
% 0.19/0.47          | ((sk_B_1)
% 0.19/0.47              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0)))
% 0.19/0.47          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.47          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.47          | ((X0) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '15'])).
% 0.19/0.47  thf('17', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('18', plain,
% 0.19/0.47      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['17'])).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.47      inference('split', [status(esa)], ['17'])).
% 0.19/0.47  thf('20', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      (![X24 : $i]:
% 0.19/0.47         (~ (r1_tarski @ (k2_relat_1 @ X24) @ sk_A)
% 0.19/0.47          | ((sk_B_1) != (k1_relat_1 @ X24))
% 0.19/0.47          | ~ (v1_funct_1 @ X24)
% 0.19/0.47          | ~ (v1_relat_1 @ X24))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.19/0.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.47        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.47  thf('23', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.47  thf('24', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.47  thf('25', plain,
% 0.19/0.47      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.47        | ((sk_B_1) != (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.19/0.47  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ?[B:$i]:
% 0.19/0.47       ( ( ![C:$i]:
% 0.19/0.47           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.19/0.47         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.48         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.48  thf('26', plain, (![X20 : $i]: ((k1_relat_1 @ (sk_B @ X20)) = (X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf(t64_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X19 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.19/0.48          | ((X19) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ X19))),
% 0.19/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) != (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.19/0.48          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.48  thf('29', plain, (![X20 : $i]: (v1_relat_1 @ (sk_B @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.48  thf('32', plain, (![X20 : $i]: (v1_relat_1 @ (sk_B @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('33', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.48      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['25', '33'])).
% 0.19/0.48  thf('35', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['30'])).
% 0.19/0.48  thf('36', plain, (![X20 : $i]: (v1_funct_1 @ (sk_B @ X20))),
% 0.19/0.48      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.19/0.48  thf('37', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.48      inference('sup+', [status(thm)], ['35', '36'])).
% 0.19/0.48  thf('38', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['34', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      ((((sk_B_1) != (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['19', '38'])).
% 0.19/0.48  thf('40', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['39'])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['17'])).
% 0.19/0.48  thf('42', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.19/0.48  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['18', '42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1)
% 0.19/0.48            != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['16', '43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((sk_B_1)
% 0.19/0.48              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1)
% 0.19/0.48            != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0)))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['45'])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i]:
% 0.19/0.48         ((v1_relat_1 @ (sk_C_2 @ X22 @ X23)) | ((X23) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf('48', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B_1)
% 0.19/0.48              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.19/0.48      inference('clc', [status(thm)], ['46', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '48'])).
% 0.19/0.48  thf('50', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['49'])).
% 0.19/0.48  thf('51', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['34', '37'])).
% 0.19/0.48  thf('52', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
