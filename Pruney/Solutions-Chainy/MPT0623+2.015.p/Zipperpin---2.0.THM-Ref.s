%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JoS8epWZTe

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:37 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 486 expanded)
%              Number of leaves         :   24 ( 144 expanded)
%              Depth                    :   19
%              Number of atoms          :  988 (4720 expanded)
%              Number of equality atoms :  166 ( 789 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
        = X19 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X18 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('6',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
        = ( k1_tarski @ X18 ) )
      | ( X19 = k1_xboole_0 ) ) ),
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

thf('13',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','19'])).

thf('21',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('23',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('26',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('28',plain,(
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('34',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','34'])).

thf('36',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['31'])).

thf('37',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('38',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('41',plain,(
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_A != X0 )
        | ( r1_tarski @ k1_xboole_0 @ X1 ) )
   <= ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ! [X1: $i] :
        ( r1_tarski @ k1_xboole_0 @ X1 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('57',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('58',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('61',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_B_1 != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B_1 != sk_B_1 )
        | ( X0 = X1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('66',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('69',plain,
    ( ( sk_B_1
      = ( k2_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('73',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('74',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('76',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','76'])).

thf('78',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('80',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('81',plain,(
    ! [X12: $i] :
      ( ( ( k1_relat_1 @ X12 )
       != k1_xboole_0 )
      | ( X12 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('82',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_1 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 )
        | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','84'])).

thf('86',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_1 )
        | ( ( sk_B @ X0 )
          = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('90',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['78','90'])).

thf('92',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('93',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('94',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','94'])).

thf('96',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','95'])).

thf('97',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','96'])).

thf('98',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('99',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(simpl_trail,[status(thm)],['56','99'])).

thf('101',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['39','100'])).

thf('102',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['21','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('104',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['105'])).

thf('107',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['102','106'])).

thf('108',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['53'])).

thf('109',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['97','98'])).

thf('110',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['108','109'])).

thf('111',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['107','110'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.15/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JoS8epWZTe
% 0.17/0.36  % Computer   : n008.cluster.edu
% 0.17/0.36  % Model      : x86_64 x86_64
% 0.17/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.36  % Memory     : 8042.1875MB
% 0.17/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.36  % CPULimit   : 60
% 0.17/0.36  % DateTime   : Tue Dec  1 15:15:45 EST 2020
% 0.17/0.36  % CPUTime    : 
% 0.17/0.36  % Running portfolio for 600 s
% 0.17/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.36  % Number of cores: 8
% 0.17/0.37  % Python version: Python 3.6.8
% 0.17/0.37  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 214 iterations in 0.130s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.40/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.60  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.40/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.60  thf(t15_funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.40/0.60       ( ![B:$i]:
% 0.40/0.60         ( ?[C:$i]:
% 0.40/0.60           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.40/0.60             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.40/0.60             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.40/0.60  thf('0', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         (((k1_relat_1 @ (sk_C_3 @ X18 @ X19)) = (X19))
% 0.40/0.60          | ((X19) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         ((v1_relat_1 @ (sk_C_3 @ X18 @ X19)) | ((X19) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.60  thf('2', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         ((v1_funct_1 @ (sk_C_3 @ X18 @ X19)) | ((X19) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.60  thf(d3_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('4', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf(d1_tarski, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X10 @ X9)
% 0.40/0.60          | ((X10) = (X7))
% 0.40/0.60          | ((X9) != (k1_tarski @ X7)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (![X7 : $i, X10 : $i]:
% 0.40/0.60         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['5'])).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.60          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['4', '6'])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('9', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.60          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.60          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.60      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.60  thf('11', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1)
% 0.40/0.60          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.40/0.60      inference('sup-', [status(thm)], ['3', '10'])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i]:
% 0.40/0.60         (((k2_relat_1 @ (sk_C_3 @ X18 @ X19)) = (k1_tarski @ X18))
% 0.40/0.60          | ((X19) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.60  thf(t18_funct_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.60          ( ![C:$i]:
% 0.40/0.60            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.60              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.40/0.60                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i]:
% 0.40/0.60        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.60             ( ![C:$i]:
% 0.40/0.60               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.60                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.40/0.60                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.40/0.60  thf('13', plain,
% 0.40/0.60      (![X20 : $i]:
% 0.40/0.60         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ X20))
% 0.40/0.60          | ~ (v1_funct_1 @ X20)
% 0.40/0.60          | ~ (v1_relat_1 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.40/0.60          | ((X1) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.40/0.60          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.60  thf('15', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ sk_A @ X0)
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.40/0.60          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.40/0.60          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.40/0.60          | ((X1) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | ((X0) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.60          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '15'])).
% 0.40/0.60  thf('17', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ sk_A @ X1)
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.60          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.40/0.60          | ((X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X0) = (k1_xboole_0))
% 0.40/0.60          | ((X0) = (k1_xboole_0))
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.60          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['1', '17'])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((r1_tarski @ sk_A @ X1)
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.60          | ((X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((sk_B_1) != (X0))
% 0.40/0.60          | ((X0) = (k1_xboole_0))
% 0.40/0.60          | ((X0) = (k1_xboole_0))
% 0.40/0.60          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '19'])).
% 0.40/0.60  thf('21', plain,
% 0.40/0.60      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.60  thf(t60_relat_1, axiom,
% 0.40/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.40/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.60  thf('22', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X20 : $i]:
% 0.40/0.60         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ X20))
% 0.40/0.60          | ~ (v1_funct_1 @ X20)
% 0.40/0.60          | ~ (v1_relat_1 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.40/0.60        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.40/0.60        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.60  thf('25', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.40/0.60        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.40/0.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.40/0.60        | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['24', '25'])).
% 0.40/0.60  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ?[B:$i]:
% 0.40/0.60       ( ( ![C:$i]:
% 0.40/0.60           ( ( r2_hidden @ C @ A ) =>
% 0.40/0.60             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.60         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.40/0.60         ( v1_relat_1 @ B ) ) ))).
% 0.40/0.60  thf('27', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf(t64_relat_1, axiom,
% 0.40/0.60    (![A:$i]:
% 0.40/0.60     ( ( v1_relat_1 @ A ) =>
% 0.40/0.60       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.60           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X12 : $i]:
% 0.40/0.60         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         (((X0) != (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.40/0.60          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.60  thf('30', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.60  thf('32', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.60  thf('33', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf('34', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.40/0.60      inference('sup+', [status(thm)], ['32', '33'])).
% 0.40/0.60  thf('35', plain,
% 0.40/0.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.40/0.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.40/0.60        | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['26', '34'])).
% 0.40/0.60  thf('36', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.40/0.60  thf('37', plain, (![X16 : $i]: (v1_funct_1 @ (sk_B @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf('38', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.40/0.60      inference('sup+', [status(thm)], ['36', '37'])).
% 0.40/0.60  thf('39', plain,
% 0.40/0.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['35', '38'])).
% 0.40/0.60  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ?[C:$i]:
% 0.40/0.60       ( ( ![D:$i]:
% 0.40/0.60           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.40/0.60         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.40/0.60         ( v1_relat_1 @ C ) ) ))).
% 0.40/0.60  thf('40', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.40/0.60  thf('41', plain,
% 0.40/0.60      (![X12 : $i]:
% 0.40/0.60         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.60  thf('42', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X0) != (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.40/0.60          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['40', '41'])).
% 0.40/0.60  thf('43', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.40/0.60  thf('44', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['42', '43'])).
% 0.40/0.60  thf('45', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('simplify', [status(thm)], ['44'])).
% 0.40/0.60  thf('46', plain,
% 0.40/0.60      (![X1 : $i, X3 : $i]:
% 0.40/0.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.60  thf('47', plain,
% 0.40/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.40/0.60         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 0.40/0.60          | ~ (r2_hidden @ X15 @ X14))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.40/0.60  thf('48', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ X0 @ X1)
% 0.40/0.60          | ((k1_funct_1 @ (sk_C_2 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.40/0.60  thf('49', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 0.40/0.60          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['45', '48'])).
% 0.40/0.60  thf('50', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 0.40/0.60          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['45', '48'])).
% 0.40/0.60  thf('51', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         (((X0) = (X1))
% 0.40/0.60          | (r1_tarski @ k1_xboole_0 @ X2)
% 0.40/0.60          | (r1_tarski @ k1_xboole_0 @ X2))),
% 0.40/0.60      inference('sup+', [status(thm)], ['49', '50'])).
% 0.40/0.60  thf('52', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.60  thf('53', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('54', plain,
% 0.40/0.60      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('55', plain,
% 0.40/0.60      ((![X0 : $i, X1 : $i]:
% 0.40/0.60          (((sk_A) != (X0)) | (r1_tarski @ k1_xboole_0 @ X1)))
% 0.40/0.60         <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['52', '54'])).
% 0.40/0.60  thf('56', plain,
% 0.40/0.60      ((![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1))
% 0.40/0.60         <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['55'])).
% 0.40/0.60  thf(d10_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.60  thf('57', plain,
% 0.40/0.60      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.40/0.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.60  thf('58', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.40/0.60      inference('simplify', [status(thm)], ['57'])).
% 0.40/0.60  thf('59', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('60', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.60         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.40/0.60      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.60  thf('61', plain,
% 0.40/0.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.60      inference('demod', [status(thm)], ['35', '38'])).
% 0.40/0.60  thf('62', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: (((X0) = (X1)) | ((sk_B_1) != (k1_xboole_0)))),
% 0.40/0.60      inference('sup-', [status(thm)], ['60', '61'])).
% 0.40/0.60  thf('63', plain,
% 0.40/0.60      ((![X0 : $i, X1 : $i]: (((sk_B_1) != (sk_B_1)) | ((X0) = (X1))))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['59', '62'])).
% 0.40/0.60  thf('64', plain,
% 0.40/0.60      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['63'])).
% 0.40/0.60  thf('65', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('66', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('67', plain,
% 0.40/0.60      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['65', '66'])).
% 0.40/0.60  thf('68', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('69', plain,
% 0.40/0.60      ((((sk_B_1) = (k2_relat_1 @ sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['67', '68'])).
% 0.40/0.60  thf('70', plain,
% 0.40/0.60      (![X20 : $i]:
% 0.40/0.60         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 0.40/0.60          | ((sk_B_1) != (k1_relat_1 @ X20))
% 0.40/0.60          | ~ (v1_funct_1 @ X20)
% 0.40/0.60          | ~ (v1_relat_1 @ X20))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('71', plain,
% 0.40/0.60      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.40/0.60         | ~ (v1_relat_1 @ sk_B_1)
% 0.40/0.60         | ~ (v1_funct_1 @ sk_B_1)
% 0.40/0.60         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['69', '70'])).
% 0.40/0.60  thf('72', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('73', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.40/0.60  thf('74', plain,
% 0.40/0.60      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['72', '73'])).
% 0.40/0.60  thf('75', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('76', plain,
% 0.40/0.60      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['74', '75'])).
% 0.40/0.60  thf('77', plain,
% 0.40/0.60      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.40/0.60         | ~ (v1_relat_1 @ sk_B_1)
% 0.40/0.60         | ~ (v1_funct_1 @ sk_B_1)
% 0.40/0.60         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['71', '76'])).
% 0.40/0.60  thf('78', plain,
% 0.40/0.60      (((~ (v1_funct_1 @ sk_B_1)
% 0.40/0.60         | ~ (v1_relat_1 @ sk_B_1)
% 0.40/0.60         | ~ (r1_tarski @ sk_B_1 @ sk_A))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['77'])).
% 0.40/0.60  thf('79', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf('80', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('81', plain,
% 0.40/0.60      (![X12 : $i]:
% 0.40/0.60         (((k1_relat_1 @ X12) != (k1_xboole_0))
% 0.40/0.60          | ((X12) = (k1_xboole_0))
% 0.40/0.60          | ~ (v1_relat_1 @ X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.40/0.60  thf('82', plain,
% 0.40/0.60      ((![X0 : $i]:
% 0.40/0.60          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.40/0.60           | ~ (v1_relat_1 @ X0)
% 0.40/0.60           | ((X0) = (k1_xboole_0))))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['80', '81'])).
% 0.40/0.60  thf('83', plain,
% 0.40/0.60      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('split', [status(esa)], ['53'])).
% 0.40/0.60  thf('84', plain,
% 0.40/0.60      ((![X0 : $i]:
% 0.40/0.60          (((k1_relat_1 @ X0) != (sk_B_1))
% 0.40/0.60           | ~ (v1_relat_1 @ X0)
% 0.40/0.60           | ((X0) = (sk_B_1))))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['82', '83'])).
% 0.40/0.60  thf('85', plain,
% 0.40/0.60      ((![X0 : $i]:
% 0.40/0.60          (((X0) != (sk_B_1))
% 0.40/0.60           | ((sk_B @ X0) = (sk_B_1))
% 0.40/0.60           | ~ (v1_relat_1 @ (sk_B @ X0))))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup-', [status(thm)], ['79', '84'])).
% 0.40/0.60  thf('86', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf('87', plain,
% 0.40/0.60      ((![X0 : $i]: (((X0) != (sk_B_1)) | ((sk_B @ X0) = (sk_B_1))))
% 0.40/0.60         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('demod', [status(thm)], ['85', '86'])).
% 0.40/0.60  thf('88', plain,
% 0.40/0.60      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('simplify', [status(thm)], ['87'])).
% 0.40/0.60  thf('89', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.60  thf('90', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.60      inference('sup+', [status(thm)], ['88', '89'])).
% 0.40/0.61  thf('91', plain,
% 0.40/0.61      (((~ (v1_funct_1 @ sk_B_1) | ~ (r1_tarski @ sk_B_1 @ sk_A)))
% 0.40/0.61         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['78', '90'])).
% 0.40/0.61  thf('92', plain,
% 0.40/0.61      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('simplify', [status(thm)], ['87'])).
% 0.40/0.61  thf('93', plain, (![X16 : $i]: (v1_funct_1 @ (sk_B @ X16))),
% 0.40/0.61      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.40/0.61  thf('94', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['92', '93'])).
% 0.40/0.61  thf('95', plain,
% 0.40/0.61      ((~ (r1_tarski @ sk_B_1 @ sk_A)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['91', '94'])).
% 0.40/0.61  thf('96', plain,
% 0.40/0.61      ((![X0 : $i]: ~ (r1_tarski @ sk_B_1 @ X0))
% 0.40/0.61         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['64', '95'])).
% 0.40/0.61  thf('97', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['58', '96'])).
% 0.40/0.61  thf('98', plain,
% 0.40/0.61      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.40/0.61      inference('split', [status(esa)], ['53'])).
% 0.40/0.61  thf('99', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.40/0.61  thf('100', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['56', '99'])).
% 0.40/0.61  thf('101', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['39', '100'])).
% 0.40/0.61  thf('102', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['21', '101'])).
% 0.40/0.61  thf('103', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.61  thf('104', plain,
% 0.40/0.61      (![X4 : $i, X6 : $i]:
% 0.40/0.61         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.61  thf('105', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         (((X1) = (X2))
% 0.40/0.61          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 0.40/0.61          | ((X0) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['103', '104'])).
% 0.40/0.61  thf('106', plain,
% 0.40/0.61      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.40/0.61      inference('condensation', [status(thm)], ['105'])).
% 0.40/0.61  thf('107', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['102', '106'])).
% 0.40/0.61  thf('108', plain,
% 0.40/0.61      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.61      inference('split', [status(esa)], ['53'])).
% 0.40/0.61  thf('109', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('sat_resolution*', [status(thm)], ['97', '98'])).
% 0.40/0.61  thf('110', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.61      inference('simpl_trail', [status(thm)], ['108', '109'])).
% 0.40/0.61  thf('111', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['107', '110'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
