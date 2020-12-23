%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xt6YuKpMqU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:40 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 202 expanded)
%              Number of leaves         :   29 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          :  794 (1853 expanded)
%              Number of equality atoms :  124 ( 315 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_4 @ X25 @ X26 ) )
        = X26 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_funct_1 @ ( sk_C_4 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
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
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_3 @ X20 @ X17 ) @ ( sk_D @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_3 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X11 != X10 )
      | ( r2_hidden @ X11 @ X12 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X10: $i] :
      ( r2_hidden @ X10 @ ( k1_tarski @ X10 ) ) ),
    inference(simplify,[status(thm)],['4'])).

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

thf('6',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_3 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( X13 = X10 )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X10: $i,X13: $i] :
      ( ( X13 = X10 )
      | ~ ( r2_hidden @ X13 @ ( k1_tarski @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C_3 @ X0 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ X25 @ X26 ) )
        = ( k1_tarski @ X25 ) )
      | ( X26 = k1_xboole_0 ) ) ),
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

thf('21',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('38',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','35','40'])).

thf('42',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

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

thf('44',plain,(
    ! [X23: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X22: $i] :
      ( ( ( k1_relat_1 @ X22 )
       != k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ( ( sk_B @ k1_xboole_0 )
        = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('51',plain,
    ( ( ~ ( v1_relat_1 @ ( sk_B @ sk_B_1 ) )
      | ( ( sk_B @ sk_B_1 )
        = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49','50'])).

thf('52',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('53',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('55',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','55'])).

thf('57',plain,
    ( ( ( sk_B @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('58',plain,(
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('59',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('62',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_relat_1 @ ( sk_C_4 @ X25 @ X26 ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_4 @ ( sk_C_3 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','68'])).

thf('70',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('72',plain,(
    ! [X27: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X8: $i] :
      ( r1_tarski @ k1_xboole_0 @ X8 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_B @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('78',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('79',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X23: $i] :
      ( v1_relat_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','81'])).

thf('83',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('84',plain,(
    ! [X23: $i] :
      ( v1_funct_1 @ ( sk_B @ X23 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('85',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['82','85'])).

thf('87',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xt6YuKpMqU
% 0.12/0.37  % Computer   : n012.cluster.edu
% 0.12/0.37  % Model      : x86_64 x86_64
% 0.12/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.37  % Memory     : 8042.1875MB
% 0.12/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.37  % CPULimit   : 60
% 0.12/0.37  % DateTime   : Tue Dec  1 11:14:22 EST 2020
% 0.12/0.37  % CPUTime    : 
% 0.12/0.37  % Running portfolio for 600 s
% 0.12/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.37  % Number of cores: 8
% 0.12/0.37  % Python version: Python 3.6.8
% 0.12/0.37  % Running in FO mode
% 0.23/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.52  % Solved by: fo/fo7.sh
% 0.23/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.52  % done 79 iterations in 0.040s
% 0.23/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.52  % SZS output start Refutation
% 0.23/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.23/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.23/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.52  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.23/0.52  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.23/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.52  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.23/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.52  thf(t15_funct_1, axiom,
% 0.23/0.52    (![A:$i]:
% 0.23/0.52     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.23/0.52       ( ![B:$i]:
% 0.23/0.52         ( ?[C:$i]:
% 0.23/0.52           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.23/0.52             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.23/0.52             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.23/0.52  thf('0', plain,
% 0.23/0.52      (![X25 : $i, X26 : $i]:
% 0.23/0.52         (((k1_relat_1 @ (sk_C_4 @ X25 @ X26)) = (X26))
% 0.23/0.52          | ((X26) = (k1_xboole_0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.23/0.52  thf('1', plain,
% 0.23/0.52      (![X25 : $i, X26 : $i]:
% 0.23/0.52         ((v1_funct_1 @ (sk_C_4 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.23/0.52  thf(d4_relat_1, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.23/0.52       ( ![C:$i]:
% 0.23/0.52         ( ( r2_hidden @ C @ B ) <=>
% 0.23/0.52           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.23/0.52  thf('2', plain,
% 0.23/0.52      (![X17 : $i, X20 : $i]:
% 0.23/0.52         (((X20) = (k1_relat_1 @ X17))
% 0.23/0.52          | (r2_hidden @ 
% 0.23/0.52             (k4_tarski @ (sk_C_3 @ X20 @ X17) @ (sk_D @ X20 @ X17)) @ X17)
% 0.23/0.52          | (r2_hidden @ (sk_C_3 @ X20 @ X17) @ X20))),
% 0.23/0.52      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.23/0.52  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.23/0.52  thf('3', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.23/0.52      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.23/0.52  thf(d1_tarski, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.52  thf('4', plain,
% 0.23/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.23/0.52         (((X11) != (X10))
% 0.23/0.52          | (r2_hidden @ X11 @ X12)
% 0.23/0.52          | ((X12) != (k1_tarski @ X10)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.52  thf('5', plain, (![X10 : $i]: (r2_hidden @ X10 @ (k1_tarski @ X10))),
% 0.23/0.52      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.52  thf(t3_xboole_0, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.23/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.23/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.23/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.23/0.52  thf('6', plain,
% 0.23/0.52      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X6 @ X4)
% 0.23/0.52          | ~ (r2_hidden @ X6 @ X7)
% 0.23/0.52          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.23/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.23/0.52  thf('7', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.52  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.52      inference('sup-', [status(thm)], ['3', '7'])).
% 0.23/0.52  thf('9', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.23/0.52          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['2', '8'])).
% 0.23/0.52  thf(t60_relat_1, axiom,
% 0.23/0.52    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.23/0.52     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.52  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.52      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.52  thf('11', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         ((r2_hidden @ (sk_C_3 @ X0 @ k1_xboole_0) @ X0)
% 0.23/0.52          | ((X0) = (k1_xboole_0)))),
% 0.23/0.52      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.52  thf(d3_tarski, axiom,
% 0.23/0.52    (![A:$i,B:$i]:
% 0.23/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.23/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.23/0.52  thf('12', plain,
% 0.23/0.52      (![X1 : $i, X3 : $i]:
% 0.23/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.52  thf('13', plain,
% 0.23/0.52      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X13 @ X12)
% 0.23/0.52          | ((X13) = (X10))
% 0.23/0.52          | ((X12) != (k1_tarski @ X10)))),
% 0.23/0.52      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.52  thf('14', plain,
% 0.23/0.52      (![X10 : $i, X13 : $i]:
% 0.23/0.52         (((X13) = (X10)) | ~ (r2_hidden @ X13 @ (k1_tarski @ X10)))),
% 0.23/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.23/0.52  thf('15', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.23/0.52          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.23/0.52      inference('sup-', [status(thm)], ['12', '14'])).
% 0.23/0.52  thf('16', plain,
% 0.23/0.52      (![X1 : $i, X3 : $i]:
% 0.23/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.23/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.23/0.52  thf('17', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.23/0.52          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.23/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.52  thf('18', plain,
% 0.23/0.52      (![X0 : $i, X1 : $i]:
% 0.23/0.52         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.52      inference('simplify', [status(thm)], ['17'])).
% 0.23/0.52  thf('19', plain,
% 0.23/0.52      (![X0 : $i]:
% 0.23/0.52         (((X0) = (k1_xboole_0))
% 0.23/0.52          | (r1_tarski @ (k1_tarski @ (sk_C_3 @ X0 @ k1_xboole_0)) @ X0))),
% 0.23/0.52      inference('sup-', [status(thm)], ['11', '18'])).
% 0.23/0.52  thf('20', plain,
% 0.23/0.52      (![X25 : $i, X26 : $i]:
% 0.23/0.52         (((k2_relat_1 @ (sk_C_4 @ X25 @ X26)) = (k1_tarski @ X25))
% 0.23/0.52          | ((X26) = (k1_xboole_0)))),
% 0.23/0.52      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.23/0.53  thf(t18_funct_1, conjecture,
% 0.23/0.53    (![A:$i,B:$i]:
% 0.23/0.53     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.53          ( ![C:$i]:
% 0.23/0.53            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.53              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.23/0.53                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.23/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.53    (~( ![A:$i,B:$i]:
% 0.23/0.53        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.53             ( ![C:$i]:
% 0.23/0.53               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.53                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.23/0.53                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.23/0.53    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.23/0.53  thf('21', plain,
% 0.23/0.53      (![X27 : $i]:
% 0.23/0.53         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.23/0.53          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.23/0.53          | ~ (v1_funct_1 @ X27)
% 0.23/0.53          | ~ (v1_relat_1 @ X27))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('22', plain,
% 0.23/0.53      (![X0 : $i, X1 : $i]:
% 0.23/0.53         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.23/0.53          | ((X1) = (k1_xboole_0))
% 0.23/0.53          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.23/0.53          | ~ (v1_funct_1 @ (sk_C_4 @ X0 @ X1))
% 0.23/0.53          | ((sk_B_1) != (k1_relat_1 @ (sk_C_4 @ X0 @ X1))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.53  thf('23', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((sk_A) = (k1_xboole_0))
% 0.23/0.53          | ((sk_B_1)
% 0.23/0.53              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.23/0.53          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.23/0.53          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.23/0.53          | ((X0) = (k1_xboole_0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['19', '22'])).
% 0.23/0.53  thf('24', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('25', plain,
% 0.23/0.53      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('26', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('27', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.53  thf('28', plain,
% 0.23/0.53      ((((k2_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['26', '27'])).
% 0.23/0.53  thf('29', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('30', plain,
% 0.23/0.53      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.23/0.53  thf('31', plain,
% 0.23/0.53      (![X27 : $i]:
% 0.23/0.53         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.23/0.53          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.23/0.53          | ~ (v1_funct_1 @ X27)
% 0.23/0.53          | ~ (v1_relat_1 @ X27))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('32', plain,
% 0.23/0.53      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.23/0.53         | ~ (v1_relat_1 @ sk_B_1)
% 0.23/0.53         | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.53         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.23/0.53  thf('33', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.23/0.53  thf('34', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.23/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.53  thf('35', plain,
% 0.23/0.53      ((![X0 : $i]: (r1_tarski @ sk_B_1 @ X0))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['33', '34'])).
% 0.23/0.53  thf('36', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('37', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.53  thf('38', plain,
% 0.23/0.53      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['36', '37'])).
% 0.23/0.53  thf('39', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('40', plain,
% 0.23/0.53      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.53  thf('41', plain,
% 0.23/0.53      (((~ (v1_relat_1 @ sk_B_1)
% 0.23/0.53         | ~ (v1_funct_1 @ sk_B_1)
% 0.23/0.53         | ((sk_B_1) != (sk_B_1)))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['32', '35', '40'])).
% 0.23/0.53  thf('42', plain,
% 0.23/0.53      (((~ (v1_funct_1 @ sk_B_1) | ~ (v1_relat_1 @ sk_B_1)))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('simplify', [status(thm)], ['41'])).
% 0.23/0.53  thf('43', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ?[B:$i]:
% 0.23/0.53       ( ( ![C:$i]:
% 0.23/0.53           ( ( r2_hidden @ C @ A ) =>
% 0.23/0.53             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.53         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.23/0.53         ( v1_relat_1 @ B ) ) ))).
% 0.23/0.53  thf('44', plain, (![X23 : $i]: ((k1_relat_1 @ (sk_B @ X23)) = (X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf(t64_relat_1, axiom,
% 0.23/0.53    (![A:$i]:
% 0.23/0.53     ( ( v1_relat_1 @ A ) =>
% 0.23/0.53       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.23/0.53           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.53  thf('45', plain,
% 0.23/0.53      (![X22 : $i]:
% 0.23/0.53         (((k1_relat_1 @ X22) != (k1_xboole_0))
% 0.23/0.53          | ((X22) = (k1_xboole_0))
% 0.23/0.53          | ~ (v1_relat_1 @ X22))),
% 0.23/0.53      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.23/0.53  thf('46', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((X0) != (k1_xboole_0))
% 0.23/0.53          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.23/0.53          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.23/0.53  thf('47', plain,
% 0.23/0.53      ((((sk_B @ k1_xboole_0) = (k1_xboole_0))
% 0.23/0.53        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.23/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.53  thf('48', plain,
% 0.23/0.53      (((~ (v1_relat_1 @ (sk_B @ sk_B_1))
% 0.23/0.53         | ((sk_B @ k1_xboole_0) = (k1_xboole_0))))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['43', '47'])).
% 0.23/0.53  thf('49', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('50', plain,
% 0.23/0.53      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('51', plain,
% 0.23/0.53      (((~ (v1_relat_1 @ (sk_B @ sk_B_1)) | ((sk_B @ sk_B_1) = (sk_B_1))))
% 0.23/0.53         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['48', '49', '50'])).
% 0.23/0.53  thf('52', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf('53', plain,
% 0.23/0.53      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.23/0.53  thf('54', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf('55', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['53', '54'])).
% 0.23/0.53  thf('56', plain,
% 0.23/0.53      ((~ (v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['42', '55'])).
% 0.23/0.53  thf('57', plain,
% 0.23/0.53      ((((sk_B @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('demod', [status(thm)], ['51', '52'])).
% 0.23/0.53  thf('58', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf('59', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.23/0.53      inference('sup+', [status(thm)], ['57', '58'])).
% 0.23/0.53  thf('60', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.23/0.53      inference('demod', [status(thm)], ['56', '59'])).
% 0.23/0.53  thf('61', plain,
% 0.23/0.53      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.23/0.53      inference('split', [status(esa)], ['24'])).
% 0.23/0.53  thf('62', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.23/0.53      inference('sat_resolution*', [status(thm)], ['60', '61'])).
% 0.23/0.53  thf('63', plain, (((sk_A) != (k1_xboole_0))),
% 0.23/0.53      inference('simpl_trail', [status(thm)], ['25', '62'])).
% 0.23/0.53  thf('64', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((sk_B_1)
% 0.23/0.53            != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.23/0.53          | ~ (v1_funct_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.23/0.53          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.23/0.53          | ((X0) = (k1_xboole_0)))),
% 0.23/0.53      inference('simplify_reflect-', [status(thm)], ['23', '63'])).
% 0.23/0.53  thf('65', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((X0) = (k1_xboole_0))
% 0.23/0.53          | ((X0) = (k1_xboole_0))
% 0.23/0.53          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.23/0.53          | ((sk_B_1)
% 0.23/0.53              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.23/0.53      inference('sup-', [status(thm)], ['1', '64'])).
% 0.23/0.53  thf('66', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((sk_B_1)
% 0.23/0.53            != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0)))
% 0.23/0.53          | ~ (v1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))
% 0.23/0.53          | ((X0) = (k1_xboole_0)))),
% 0.23/0.53      inference('simplify', [status(thm)], ['65'])).
% 0.23/0.53  thf('67', plain,
% 0.23/0.53      (![X25 : $i, X26 : $i]:
% 0.23/0.53         ((v1_relat_1 @ (sk_C_4 @ X25 @ X26)) | ((X26) = (k1_xboole_0)))),
% 0.23/0.53      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.23/0.53  thf('68', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((X0) = (k1_xboole_0))
% 0.23/0.53          | ((sk_B_1)
% 0.23/0.53              != (k1_relat_1 @ (sk_C_4 @ (sk_C_3 @ sk_A @ k1_xboole_0) @ X0))))),
% 0.23/0.53      inference('clc', [status(thm)], ['66', '67'])).
% 0.23/0.53  thf('69', plain,
% 0.23/0.53      (![X0 : $i]:
% 0.23/0.53         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['0', '68'])).
% 0.23/0.53  thf('70', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.23/0.53      inference('simplify', [status(thm)], ['69'])).
% 0.23/0.53  thf('71', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.53  thf('72', plain,
% 0.23/0.53      (![X27 : $i]:
% 0.23/0.53         (~ (r1_tarski @ (k2_relat_1 @ X27) @ sk_A)
% 0.23/0.53          | ((sk_B_1) != (k1_relat_1 @ X27))
% 0.23/0.53          | ~ (v1_funct_1 @ X27)
% 0.23/0.53          | ~ (v1_relat_1 @ X27))),
% 0.23/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.53  thf('73', plain,
% 0.23/0.53      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.23/0.53        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.23/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.23/0.53        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.23/0.53      inference('sup-', [status(thm)], ['71', '72'])).
% 0.23/0.53  thf('74', plain, (![X8 : $i]: (r1_tarski @ k1_xboole_0 @ X8)),
% 0.23/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.23/0.53  thf('75', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.23/0.53  thf('76', plain,
% 0.23/0.53      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.23/0.53        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.23/0.53        | ((sk_B_1) != (k1_xboole_0)))),
% 0.23/0.53      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.23/0.53  thf('77', plain,
% 0.23/0.53      ((((sk_B @ k1_xboole_0) = (k1_xboole_0))
% 0.23/0.53        | ~ (v1_relat_1 @ (sk_B @ k1_xboole_0)))),
% 0.23/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.23/0.53  thf('78', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf('79', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.23/0.53  thf('80', plain, (![X23 : $i]: (v1_relat_1 @ (sk_B @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.23/0.53      inference('sup+', [status(thm)], ['79', '80'])).
% 0.23/0.53  thf('82', plain,
% 0.23/0.53      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_1) != (k1_xboole_0)))),
% 0.23/0.53      inference('demod', [status(thm)], ['76', '81'])).
% 0.23/0.53  thf('83', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['77', '78'])).
% 0.23/0.53  thf('84', plain, (![X23 : $i]: (v1_funct_1 @ (sk_B @ X23))),
% 0.23/0.53      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.23/0.53  thf('85', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.23/0.53      inference('sup+', [status(thm)], ['83', '84'])).
% 0.23/0.53  thf('86', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.23/0.53      inference('demod', [status(thm)], ['82', '85'])).
% 0.23/0.53  thf('87', plain, ($false),
% 0.23/0.53      inference('simplify_reflect-', [status(thm)], ['70', '86'])).
% 0.23/0.53  
% 0.23/0.53  % SZS output end Refutation
% 0.23/0.53  
% 0.23/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
