%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kuYGT9D31m

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 160 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  566 (1451 expanded)
%              Number of equality atoms :  106 ( 264 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ ( sk_C @ X8 @ X9 ) )
        = X9 )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_funct_1 @ ( sk_C @ X8 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
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
    ! [X2: $i,X4: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X2 ) @ X4 )
      | ~ ( r2_hidden @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( sk_C @ X8 @ X9 ) )
        = ( k1_tarski @ X8 ) )
      | ( X9 = k1_xboole_0 ) ) ),
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
    ! [X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C @ X0 @ X1 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

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

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('12',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,
    ( ( ( k2_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ~ ( r1_tarski @ sk_B_2 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_B_2
       != ( k1_relat_1 @ sk_B_2 ) ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_2 @ X0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

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
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X6 ) )
      = X6 ) ),
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
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X6 ) ) ),
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
    ! [X6: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('29',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_relat_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','29'])).

thf('31',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('32',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('33',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('35',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('37',plain,
    ( ( v1_funct_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_B_2 != sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','20','30','37','42'])).

thf('44',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X8: $i,X9: $i] :
      ( ( v1_relat_1 @ ( sk_C @ X8 @ X9 ) )
      | ( X9 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('56',plain,(
    ! [X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('59',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('60',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['26'])).

thf('61',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('62',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('64',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['57','58','59','62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kuYGT9D31m
% 0.11/0.32  % Computer   : n014.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 17:21:37 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.32  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 48 iterations in 0.022s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.46  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(t15_funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ?[C:$i]:
% 0.19/0.46           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.19/0.46             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.46             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         (((k1_relat_1 @ (sk_C @ X8 @ X9)) = (X9)) | ((X9) = (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         ((v1_funct_1 @ (sk_C @ X8 @ X9)) | ((X9) = (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.46  thf(t7_xboole_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.46          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.46  thf(l1_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X2 : $i, X4 : $i]:
% 0.19/0.46         ((r1_tarski @ (k1_tarski @ X2) @ X4) | ~ (r2_hidden @ X2 @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         (((k2_relat_1 @ (sk_C @ X8 @ X9)) = (k1_tarski @ X8))
% 0.19/0.46          | ((X9) = (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.46  thf(t18_funct_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.46          ( ![C:$i]:
% 0.19/0.46            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.46                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.46             ( ![C:$i]:
% 0.19/0.46               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.46                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.46                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X10 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X10) @ sk_A)
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ X10))
% 0.19/0.46          | ~ (v1_funct_1 @ X10)
% 0.19/0.46          | ~ (v1_relat_1 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.19/0.46          | ((X1) = (k1_xboole_0))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_C @ X0 @ X1))
% 0.19/0.46          | ~ (v1_funct_1 @ (sk_C @ X0 @ X1))
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ X0 @ X1))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((sk_A) = (k1_xboole_0))
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.19/0.46          | ~ (v1_funct_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.19/0.46          | ((X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.46  thf('9', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain,
% 0.19/0.46      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('11', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf(t60_relat_1, axiom,
% 0.19/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf('12', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      ((((k2_relat_1 @ sk_B_2) = (k1_xboole_0)))
% 0.19/0.46         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['11', '12'])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      ((((k2_relat_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X10 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X10) @ sk_A)
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ X10))
% 0.19/0.46          | ~ (v1_funct_1 @ X10)
% 0.19/0.46          | ~ (v1_relat_1 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (((~ (r1_tarski @ sk_B_2 @ sk_A)
% 0.19/0.46         | ~ (v1_relat_1 @ sk_B_2)
% 0.19/0.46         | ~ (v1_funct_1 @ sk_B_2)
% 0.19/0.46         | ((sk_B_2) != (k1_relat_1 @ sk_B_2))))
% 0.19/0.46         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.46  thf('19', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      ((![X0 : $i]: (r1_tarski @ sk_B_2 @ X0))
% 0.19/0.46         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ?[B:$i]:
% 0.19/0.46       ( ( ![C:$i]:
% 0.19/0.46           ( ( r2_hidden @ C @ A ) =>
% 0.19/0.46             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.46         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.46         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.46  thf('22', plain, (![X6 : $i]: ((k1_relat_1 @ (sk_B_1 @ X6)) = (X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf(t64_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.46           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.46         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X5 : $i]:
% 0.19/0.46         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 0.19/0.46          | ((X5) = (k1_xboole_0))
% 0.19/0.46          | ~ (v1_relat_1 @ X5))),
% 0.19/0.46      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.46  thf('24', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) != (k1_xboole_0))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.19/0.46          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.46  thf('25', plain, (![X6 : $i]: (v1_relat_1 @ (sk_B_1 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.46  thf('27', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.46  thf('28', plain, (![X6 : $i]: (v1_relat_1 @ (sk_B_1 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('29', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.46      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.46  thf('30', plain, (((v1_relat_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['21', '29'])).
% 0.19/0.46  thf('31', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('32', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.46  thf('33', plain,
% 0.19/0.46      ((((sk_B_1 @ sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['31', '32'])).
% 0.19/0.46  thf('34', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('35', plain,
% 0.19/0.46      ((((sk_B_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['33', '34'])).
% 0.19/0.46  thf('36', plain, (![X6 : $i]: (v1_funct_1 @ (sk_B_1 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('37', plain, (((v1_funct_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['35', '36'])).
% 0.19/0.46  thf('38', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.46  thf('40', plain,
% 0.19/0.46      ((((k1_relat_1 @ sk_B_2) = (k1_xboole_0)))
% 0.19/0.46         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.46  thf('41', plain,
% 0.19/0.46      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('42', plain,
% 0.19/0.46      ((((k1_relat_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.46  thf('43', plain,
% 0.19/0.46      ((((sk_B_2) != (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.19/0.46      inference('demod', [status(thm)], ['17', '20', '30', '37', '42'])).
% 0.19/0.46  thf('44', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.46  thf('45', plain,
% 0.19/0.46      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_2) = (k1_xboole_0)))),
% 0.19/0.46      inference('split', [status(esa)], ['9'])).
% 0.19/0.46  thf('46', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.46      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 0.19/0.46  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.46      inference('simpl_trail', [status(thm)], ['10', '46'])).
% 0.19/0.46  thf('48', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.19/0.46          | ~ (v1_funct_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.19/0.46          | ((X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['8', '47'])).
% 0.19/0.46  thf('49', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) = (k1_xboole_0))
% 0.19/0.46          | ((X0) = (k1_xboole_0))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '48'])).
% 0.19/0.46  thf('50', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0)))
% 0.19/0.46          | ~ (v1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))
% 0.19/0.46          | ((X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('simplify', [status(thm)], ['49'])).
% 0.19/0.46  thf('51', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         ((v1_relat_1 @ (sk_C @ X8 @ X9)) | ((X9) = (k1_xboole_0)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.46  thf('52', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((X0) = (k1_xboole_0))
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ (sk_C @ (sk_B @ sk_A) @ X0))))),
% 0.19/0.46      inference('clc', [status(thm)], ['50', '51'])).
% 0.19/0.46  thf('53', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (((sk_B_2) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '52'])).
% 0.19/0.46  thf('54', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['53'])).
% 0.19/0.46  thf('55', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.46  thf('56', plain,
% 0.19/0.46      (![X10 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X10) @ sk_A)
% 0.19/0.46          | ((sk_B_2) != (k1_relat_1 @ X10))
% 0.19/0.46          | ~ (v1_funct_1 @ X10)
% 0.19/0.46          | ~ (v1_relat_1 @ X10))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('57', plain,
% 0.19/0.46      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.19/0.46        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.46        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.46        | ((sk_B_2) != (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['55', '56'])).
% 0.19/0.46  thf('58', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.46  thf('59', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.46      inference('sup+', [status(thm)], ['27', '28'])).
% 0.19/0.46  thf('60', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('simplify', [status(thm)], ['26'])).
% 0.19/0.46  thf('61', plain, (![X6 : $i]: (v1_funct_1 @ (sk_B_1 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.46  thf('62', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.19/0.46      inference('sup+', [status(thm)], ['60', '61'])).
% 0.19/0.46  thf('63', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.46  thf('64', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['57', '58', '59', '62', '63'])).
% 0.19/0.46  thf('65', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['54', '64'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
