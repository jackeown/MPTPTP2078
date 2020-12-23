%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7lsngT7gdG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:22 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 294 expanded)
%              Number of leaves         :   23 (  96 expanded)
%              Depth                    :   18
%              Number of atoms          :  579 (2717 expanded)
%              Number of equality atoms :   38 ( 168 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_4 @ X20 @ X17 ) @ ( sk_D_1 @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_4 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t7_tarski,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ! [D: $i] :
                  ~ ( ( r2_hidden @ D @ B )
                    & ( r2_hidden @ D @ C ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_4 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X1 ) @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( X0
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ ( sk_C_5 @ X22 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t19_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ X0 ) @ X1 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_5 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_5 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('18',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('22',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_5 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','26'])).

thf('28',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_2 @ X19 @ X17 ) ) @ X17 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('30',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_2 @ X19 @ X17 ) ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_2 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( ( k1_xboole_0
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ( r2_hidden @ ( sk_C_5 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D_2 @ ( sk_C @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('33',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['33'])).

thf('40',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['34','40'])).

thf('42',plain,
    ( ( r2_hidden @ ( sk_C_5 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D_2 @ ( sk_C @ ( k2_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['32','41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('44',plain,
    ( ( r2_hidden @ ( sk_C_5 @ k1_xboole_0 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ ( sk_C_2 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_tarski])).

thf('46',plain,(
    r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C_1 @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ( r2_hidden @ ( sk_C_1 @ X3 @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['49','57'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['46','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7lsngT7gdG
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.52/0.69  % Solved by: fo/fo7.sh
% 0.52/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.69  % done 325 iterations in 0.262s
% 0.52/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.52/0.69  % SZS output start Refutation
% 0.52/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.69  thf(sk_C_5_type, type, sk_C_5: $i > $i).
% 0.52/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.69  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.52/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.52/0.69  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.52/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.69  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.52/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.69  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.52/0.69  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.52/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.52/0.69  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.52/0.69  thf('0', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.52/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.69  thf(d4_relat_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.52/0.69       ( ![C:$i]:
% 0.52/0.69         ( ( r2_hidden @ C @ B ) <=>
% 0.52/0.69           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.52/0.69  thf('1', plain,
% 0.52/0.69      (![X17 : $i, X20 : $i]:
% 0.52/0.69         (((X20) = (k1_relat_1 @ X17))
% 0.52/0.69          | (r2_hidden @ 
% 0.52/0.69             (k4_tarski @ (sk_C_4 @ X20 @ X17) @ (sk_D_1 @ X20 @ X17)) @ X17)
% 0.52/0.69          | (r2_hidden @ (sk_C_4 @ X20 @ X17) @ X20))),
% 0.52/0.69      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.69  thf(t7_tarski, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ~( ( r2_hidden @ A @ B ) & 
% 0.52/0.69          ( ![C:$i]:
% 0.52/0.69            ( ~( ( r2_hidden @ C @ B ) & 
% 0.52/0.69                 ( ![D:$i]:
% 0.52/0.69                   ( ~( ( r2_hidden @ D @ B ) & ( r2_hidden @ D @ C ) ) ) ) ) ) ) ) ))).
% 0.52/0.69  thf('2', plain,
% 0.52/0.69      (![X7 : $i, X8 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.69  thf('3', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_4 @ X1 @ X0) @ X1)
% 0.52/0.69          | ((X1) = (k1_relat_1 @ X0))
% 0.52/0.69          | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.52/0.69  thf('4', plain,
% 0.52/0.69      (![X7 : $i, X8 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.69  thf('5', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_2 @ X1) @ X1)
% 0.52/0.69          | ((X0) = (k1_relat_1 @ X1))
% 0.52/0.69          | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.52/0.69  thf('6', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_2 @ X0) @ X0) | ((X0) = (k1_relat_1 @ X0)))),
% 0.52/0.69      inference('eq_fact', [status(thm)], ['5'])).
% 0.52/0.69  thf('7', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_2 @ X0) @ X0) | ((X0) = (k1_relat_1 @ X0)))),
% 0.52/0.69      inference('eq_fact', [status(thm)], ['5'])).
% 0.52/0.69  thf(t3_xboole_0, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.52/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.52/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.52/0.69  thf('8', plain,
% 0.52/0.69      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.69          | ~ (r2_hidden @ X4 @ X5)
% 0.52/0.69          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.69  thf('9', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (((X0) = (k1_relat_1 @ X0))
% 0.52/0.69          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.52/0.69          | ~ (r2_hidden @ (sk_C_2 @ X0) @ X1))),
% 0.52/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.52/0.69  thf('10', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         (((X0) = (k1_relat_1 @ X0))
% 0.52/0.69          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.52/0.69          | ((X0) = (k1_relat_1 @ X0)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['6', '9'])).
% 0.52/0.69  thf('11', plain,
% 0.52/0.69      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | ((X0) = (k1_relat_1 @ X0)))),
% 0.52/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.52/0.69  thf('12', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['0', '11'])).
% 0.52/0.69  thf(t2_tarski, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.52/0.69       ( ( A ) = ( B ) ) ))).
% 0.52/0.69  thf('13', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (((X1) = (X0))
% 0.52/0.69          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.52/0.69          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.52/0.69      inference('cnf', [status(esa)], [t2_tarski])).
% 0.52/0.69  thf(t19_relat_1, axiom,
% 0.52/0.69    (![A:$i,B:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ B ) =>
% 0.52/0.69       ( ~( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) & 
% 0.52/0.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k1_relat_1 @ B ) ) ) ) ) ) ))).
% 0.52/0.69  thf('14', plain,
% 0.52/0.69      (![X22 : $i, X23 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_5 @ X22) @ (k1_relat_1 @ X22))
% 0.52/0.69          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X22))
% 0.52/0.69          | ~ (v1_relat_1 @ X22))),
% 0.52/0.69      inference('cnf', [status(esa)], [t19_relat_1])).
% 0.52/0.69  thf('15', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C @ (k2_relat_1 @ X0) @ X1) @ X1)
% 0.52/0.69          | ((X1) = (k2_relat_1 @ X0))
% 0.52/0.69          | ~ (v1_relat_1 @ X0)
% 0.52/0.69          | (r2_hidden @ (sk_C_5 @ X0) @ (k1_relat_1 @ X0)))),
% 0.52/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.52/0.69  thf('16', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_5 @ k1_xboole_0) @ k1_xboole_0)
% 0.52/0.69          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.52/0.69          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.52/0.69          | (r2_hidden @ (sk_C @ (k2_relat_1 @ k1_xboole_0) @ X0) @ X0))),
% 0.52/0.69      inference('sup+', [status(thm)], ['12', '15'])).
% 0.52/0.69  thf('17', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.52/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.69  thf(d1_relat_1, axiom,
% 0.52/0.69    (![A:$i]:
% 0.52/0.69     ( ( v1_relat_1 @ A ) <=>
% 0.52/0.69       ( ![B:$i]:
% 0.52/0.69         ( ~( ( r2_hidden @ B @ A ) & 
% 0.52/0.69              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.52/0.69  thf('18', plain,
% 0.52/0.69      (![X12 : $i]: ((v1_relat_1 @ X12) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.52/0.69      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.52/0.69  thf('19', plain,
% 0.52/0.69      (![X7 : $i, X8 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.69  thf('20', plain,
% 0.52/0.69      (![X0 : $i]: ((v1_relat_1 @ X0) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.69  thf('21', plain,
% 0.52/0.69      (![X0 : $i]: ((v1_relat_1 @ X0) | (r2_hidden @ (sk_C_2 @ X0) @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.52/0.69  thf('22', plain,
% 0.52/0.69      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.69          | ~ (r2_hidden @ X4 @ X5)
% 0.52/0.69          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.69  thf('23', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((v1_relat_1 @ X0)
% 0.52/0.69          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.52/0.69          | ~ (r2_hidden @ (sk_C_2 @ X0) @ X1))),
% 0.52/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.52/0.69  thf('24', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((v1_relat_1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0) | (v1_relat_1 @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['20', '23'])).
% 0.52/0.69  thf('25', plain,
% 0.52/0.69      (![X0 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (v1_relat_1 @ X0))),
% 0.52/0.69      inference('simplify', [status(thm)], ['24'])).
% 0.52/0.69  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.52/0.69      inference('sup-', [status(thm)], ['17', '25'])).
% 0.52/0.69  thf('27', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         ((r2_hidden @ (sk_C_5 @ k1_xboole_0) @ k1_xboole_0)
% 0.52/0.69          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 0.52/0.69          | (r2_hidden @ (sk_C @ (k2_relat_1 @ k1_xboole_0) @ X0) @ X0))),
% 0.52/0.69      inference('demod', [status(thm)], ['16', '26'])).
% 0.52/0.69  thf('28', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['0', '11'])).
% 0.52/0.69  thf('29', plain,
% 0.52/0.69      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X19 @ X18)
% 0.52/0.69          | (r2_hidden @ (k4_tarski @ X19 @ (sk_D_2 @ X19 @ X17)) @ X17)
% 0.52/0.69          | ((X18) != (k1_relat_1 @ X17)))),
% 0.52/0.69      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.52/0.69  thf('30', plain,
% 0.52/0.69      (![X17 : $i, X19 : $i]:
% 0.52/0.69         ((r2_hidden @ (k4_tarski @ X19 @ (sk_D_2 @ X19 @ X17)) @ X17)
% 0.52/0.69          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X17)))),
% 0.52/0.69      inference('simplify', [status(thm)], ['29'])).
% 0.52/0.69  thf('31', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.52/0.69          | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_2 @ X0 @ k1_xboole_0)) @ 
% 0.52/0.69             k1_xboole_0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['28', '30'])).
% 0.52/0.69  thf('32', plain,
% 0.52/0.69      ((((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.52/0.69        | (r2_hidden @ (sk_C_5 @ k1_xboole_0) @ k1_xboole_0)
% 0.52/0.69        | (r2_hidden @ 
% 0.52/0.69           (k4_tarski @ (sk_C @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.52/0.69            (sk_D_2 @ (sk_C @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.52/0.69             k1_xboole_0)) @ 
% 0.52/0.69           k1_xboole_0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['27', '31'])).
% 0.52/0.69  thf(t60_relat_1, conjecture,
% 0.52/0.69    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.69     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.52/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.69    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.52/0.69        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.52/0.69    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.52/0.69  thf('33', plain,
% 0.52/0.69      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.52/0.69        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.52/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.69  thf('34', plain,
% 0.52/0.69      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.69         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['33'])).
% 0.52/0.69  thf('35', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['0', '11'])).
% 0.52/0.69  thf('36', plain,
% 0.52/0.69      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.69         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.69      inference('split', [status(esa)], ['33'])).
% 0.52/0.69  thf('37', plain,
% 0.52/0.69      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.69         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.52/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.52/0.69  thf('38', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.69      inference('simplify', [status(thm)], ['37'])).
% 0.52/0.69  thf('39', plain,
% 0.52/0.69      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.52/0.69       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.69      inference('split', [status(esa)], ['33'])).
% 0.52/0.69  thf('40', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.69      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.52/0.69  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.52/0.69      inference('simpl_trail', [status(thm)], ['34', '40'])).
% 0.52/0.69  thf('42', plain,
% 0.52/0.69      (((r2_hidden @ (sk_C_5 @ k1_xboole_0) @ k1_xboole_0)
% 0.52/0.69        | (r2_hidden @ 
% 0.52/0.69           (k4_tarski @ (sk_C @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.52/0.69            (sk_D_2 @ (sk_C @ (k2_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.52/0.69             k1_xboole_0)) @ 
% 0.52/0.69           k1_xboole_0))),
% 0.52/0.69      inference('simplify_reflect-', [status(thm)], ['32', '41'])).
% 0.52/0.69  thf('43', plain,
% 0.52/0.69      (![X7 : $i, X8 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.69  thf('44', plain,
% 0.52/0.69      (((r2_hidden @ (sk_C_5 @ k1_xboole_0) @ k1_xboole_0)
% 0.52/0.69        | (r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.69  thf('45', plain,
% 0.52/0.69      (![X7 : $i, X8 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X7 @ X8) | (r2_hidden @ (sk_C_2 @ X8) @ X8))),
% 0.52/0.69      inference('cnf', [status(esa)], [t7_tarski])).
% 0.52/0.69  thf('46', plain, ((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)),
% 0.52/0.69      inference('clc', [status(thm)], ['44', '45'])).
% 0.52/0.69  thf('47', plain, ((r2_hidden @ (sk_C_2 @ k1_xboole_0) @ k1_xboole_0)),
% 0.52/0.69      inference('clc', [status(thm)], ['44', '45'])).
% 0.52/0.69  thf('48', plain,
% 0.52/0.69      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.69          | ~ (r2_hidden @ X4 @ X5)
% 0.52/0.69          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.69  thf('49', plain,
% 0.52/0.69      (![X0 : $i]:
% 0.52/0.69         (~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.69          | ~ (r2_hidden @ (sk_C_2 @ k1_xboole_0) @ X0))),
% 0.52/0.69      inference('sup-', [status(thm)], ['47', '48'])).
% 0.52/0.69  thf('50', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.52/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.52/0.69  thf('51', plain,
% 0.52/0.69      (![X2 : $i, X3 : $i]:
% 0.52/0.69         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C_1 @ X3 @ X2) @ X2))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.69  thf('52', plain,
% 0.52/0.69      (![X2 : $i, X3 : $i]:
% 0.52/0.69         ((r1_xboole_0 @ X2 @ X3) | (r2_hidden @ (sk_C_1 @ X3 @ X2) @ X2))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.69  thf('53', plain,
% 0.52/0.69      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.52/0.69         (~ (r2_hidden @ X4 @ X2)
% 0.52/0.69          | ~ (r2_hidden @ X4 @ X5)
% 0.52/0.69          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.52/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.69  thf('54', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.69         ((r1_xboole_0 @ X0 @ X1)
% 0.52/0.69          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.52/0.69          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 0.52/0.69      inference('sup-', [status(thm)], ['52', '53'])).
% 0.52/0.69  thf('55', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         ((r1_xboole_0 @ X0 @ X1)
% 0.52/0.69          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.52/0.69          | (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('sup-', [status(thm)], ['51', '54'])).
% 0.52/0.69  thf('56', plain,
% 0.52/0.69      (![X0 : $i, X1 : $i]:
% 0.52/0.69         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.69      inference('simplify', [status(thm)], ['55'])).
% 0.52/0.69  thf('57', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.52/0.69      inference('sup-', [status(thm)], ['50', '56'])).
% 0.52/0.69  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ (sk_C_2 @ k1_xboole_0) @ X0)),
% 0.52/0.69      inference('demod', [status(thm)], ['49', '57'])).
% 0.52/0.69  thf('59', plain, ($false), inference('sup-', [status(thm)], ['46', '58'])).
% 0.52/0.69  
% 0.52/0.69  % SZS output end Refutation
% 0.52/0.69  
% 0.52/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
