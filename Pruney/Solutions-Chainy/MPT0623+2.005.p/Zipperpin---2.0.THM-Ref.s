%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ncLlH1hV0q

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 153 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   22
%              Number of atoms          :  655 (1270 expanded)
%              Number of equality atoms :  105 ( 215 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_1 @ X15 @ X16 ) )
        = X16 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_funct_1 @ ( sk_C_1 @ X15 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X6 ) @ X8 )
      | ~ ( r2_hidden @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_1 @ X15 @ X16 ) )
        = ( k1_tarski @ X15 ) )
      | ( X16 = k1_xboole_0 ) ) ),
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
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
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

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('11',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('13',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('17',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('21',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','24'])).

thf('26',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( r1_tarski @ sk_B_1 @ sk_A ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X11 )
      | ~ ( r2_hidden @ X9 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','36'])).

thf('38',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','37'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('45',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['9'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['45','46'])).

thf('48',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['10','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['8','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_relat_1 @ ( sk_C_1 @ X15 @ X16 ) )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_1 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','53'])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X14: $i] :
      ( ( v1_funct_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf('57',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('58',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('59',plain,(
    ! [X17: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('65',plain,(
    ! [X10: $i,X11: $i] :
      ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X10 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('66',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ncLlH1hV0q
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 61 iterations in 0.031s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.48  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(t15_funct_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ?[C:$i]:
% 0.19/0.48           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.19/0.48             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.48             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (((k1_relat_1 @ (sk_C_1 @ X15 @ X16)) = (X16))
% 0.19/0.48          | ((X16) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((v1_funct_1 @ (sk_C_1 @ X15 @ X16)) | ((X16) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf(t7_xboole_0, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.19/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.48  thf(l1_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X6 : $i, X8 : $i]:
% 0.19/0.48         ((r1_tarski @ (k1_tarski @ X6) @ X8) | ~ (r2_hidden @ X6 @ X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.48  thf('5', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         (((k2_relat_1 @ (sk_C_1 @ X15 @ X16)) = (k1_tarski @ X15))
% 0.19/0.48          | ((X16) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf(t18_funct_1, conjecture,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.48          ( ![C:$i]:
% 0.19/0.48            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.48                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i,B:$i]:
% 0.19/0.48        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.48             ( ![C:$i]:
% 0.19/0.48               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.48                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.19/0.48                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X17 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ X17))
% 0.19/0.48          | ~ (v1_funct_1 @ X17)
% 0.19/0.48          | ~ (v1_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.19/0.48          | ((X1) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ X0 @ X1))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ X0 @ X1))
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ X0 @ X1))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_A) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.48  thf('9', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf(cc1_relat_1, axiom,
% 0.19/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.19/0.48  thf('11', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.48  thf(cc1_funct_1, axiom,
% 0.19/0.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.19/0.48  thf('12', plain, (![X14 : $i]: ((v1_funct_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf(t60_relat_1, axiom,
% 0.19/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('14', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('15', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      (![X17 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ X17))
% 0.19/0.48          | ~ (v1_funct_1 @ X17)
% 0.19/0.48          | ~ (v1_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.19/0.48         | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.48         | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.48         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('21', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('24', plain,
% 0.19/0.48      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.48  thf('25', plain,
% 0.19/0.48      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.19/0.48         | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.48         | ~ (v1_funct_1 @ sk_B_1)
% 0.19/0.48         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['19', '24'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (((~ (v1_funct_1 @ sk_B_1)
% 0.19/0.48         | ~ (v1_relat_1 @ sk_B_1)
% 0.19/0.48         | ~ (r1_tarski @ sk_B_1 @ sk_A))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.19/0.48  thf(d3_tarski, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf(t4_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((![X0 : $i]: ((k4_xboole_0 @ sk_B_1 @ X0) = (k1_xboole_0)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      ((![X0 : $i]: ((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf(t64_zfmisc_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.19/0.48       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.19/0.48         (((X9) != (X11))
% 0.19/0.48          | ~ (r2_hidden @ X9 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11))))),
% 0.19/0.48      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]:
% 0.19/0.48         ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['32', '34'])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['27', '35'])).
% 0.19/0.48  thf('37', plain,
% 0.19/0.48      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['26', '36'])).
% 0.19/0.48  thf('38', plain,
% 0.19/0.48      (((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.19/0.48         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['12', '37'])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('demod', [status(thm)], ['38', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['11', '42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('45', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.19/0.48      inference('split', [status(esa)], ['9'])).
% 0.19/0.48  thf('47', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sat_resolution*', [status(thm)], ['45', '46'])).
% 0.19/0.48  thf('48', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.48      inference('simpl_trail', [status(thm)], ['10', '47'])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.19/0.48          | ~ (v1_funct_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['8', '48'])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((X0) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '49'])).
% 0.19/0.48  thf('51', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0)))
% 0.19/0.48          | ~ (v1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))
% 0.19/0.48          | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['50'])).
% 0.19/0.48  thf('52', plain,
% 0.19/0.48      (![X15 : $i, X16 : $i]:
% 0.19/0.48         ((v1_relat_1 @ (sk_C_1 @ X15 @ X16)) | ((X16) = (k1_xboole_0)))),
% 0.19/0.48      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((X0) = (k1_xboole_0))
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ (sk_C_1 @ (sk_B @ sk_A) @ X0))))),
% 0.19/0.48      inference('clc', [status(thm)], ['51', '52'])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '53'])).
% 0.19/0.48  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.19/0.48      inference('simplify', [status(thm)], ['54'])).
% 0.19/0.48  thf('56', plain, (![X14 : $i]: ((v1_funct_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.19/0.48  thf('57', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.48  thf('58', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      (![X17 : $i]:
% 0.19/0.48         (~ (r1_tarski @ (k2_relat_1 @ X17) @ sk_A)
% 0.19/0.48          | ((sk_B_1) != (k1_relat_1 @ X17))
% 0.19/0.48          | ~ (v1_funct_1 @ X17)
% 0.19/0.48          | ~ (v1_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.19/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.48        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['58', '59'])).
% 0.19/0.48  thf('61', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.48  thf('62', plain,
% 0.19/0.48      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.19/0.48        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.48        | ((sk_B_1) != (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['60', '61'])).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      (![X1 : $i, X3 : $i]:
% 0.19/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      (![X5 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.19/0.48  thf('65', plain,
% 0.19/0.48      (![X10 : $i, X11 : $i]:
% 0.19/0.48         ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X10 @ (k1_tarski @ X11)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.48  thf('66', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['64', '65'])).
% 0.19/0.48  thf('67', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['63', '66'])).
% 0.19/0.48  thf('68', plain,
% 0.19/0.48      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.48        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.19/0.48        | ((sk_B_1) != (k1_xboole_0)))),
% 0.19/0.48      inference('demod', [status(thm)], ['62', '67'])).
% 0.19/0.48  thf('69', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.48        | ((sk_B_1) != (k1_xboole_0))
% 0.19/0.48        | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['57', '68'])).
% 0.19/0.48  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('71', plain,
% 0.19/0.48      ((((sk_B_1) != (k1_xboole_0)) | ~ (v1_funct_1 @ k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.48  thf('72', plain,
% 0.19/0.48      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['56', '71'])).
% 0.19/0.48  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('74', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['72', '73'])).
% 0.19/0.48  thf('75', plain, ($false),
% 0.19/0.48      inference('simplify_reflect-', [status(thm)], ['55', '74'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
