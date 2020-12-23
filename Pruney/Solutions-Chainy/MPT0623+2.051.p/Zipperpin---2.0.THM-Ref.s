%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I7wR4SFQte

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 178 expanded)
%              Number of leaves         :   24 (  59 expanded)
%              Depth                    :   20
%              Number of atoms          :  715 (1652 expanded)
%              Number of equality atoms :  128 ( 298 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X14: $i,X15: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
        = X15 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_funct_1 @ ( sk_C_2 @ X14 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X9 @ X8 )
      | ( X9 = X6 )
      | ( X8
       != ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X6: $i,X9: $i] :
      ( ( X9 = X6 )
      | ~ ( r2_hidden @ X9 @ ( k1_tarski @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
        = ( k1_tarski @ X14 ) )
      | ( X15 = k1_xboole_0 ) ) ),
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

thf('12',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('21',plain,
    ( ( ( k2_relat_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ~ ( r1_tarski @ sk_B_2 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_B_2
       != ( k1_relat_1 @ sk_B_2 ) ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B_2 @ X0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_2 )
      | ~ ( v1_funct_1 @ sk_B_2 )
      | ( sk_B_2 != sk_B_2 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26','31'])).

thf('33',plain,
    ( ( ~ ( v1_funct_1 @ sk_B_2 )
      | ~ ( v1_relat_1 @ sk_B_2 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

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

thf('34',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('35',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('36',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('37',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_2 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B_2 )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B_2 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_2 )
        | ( ( sk_B_1 @ X0 )
          = sk_B_2 )
        | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( X0 != sk_B_2 )
        | ( ( sk_B_1 @ X0 )
          = sk_B_2 ) )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('45',plain,
    ( ( v1_relat_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','45'])).

thf('47',plain,
    ( ( ( sk_B_1 @ sk_B_2 )
      = sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['42'])).

thf('48',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('49',plain,
    ( ( v1_funct_1 @ sk_B_2 )
   <= ( sk_B_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_relat_1 @ ( sk_C_2 @ X14 @ X15 ) )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_2
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( sk_B_2 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','58'])).

thf('60',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('62',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B_2
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('66',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('68',plain,(
    ! [X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( X11 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X12: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('74',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','74'])).

thf('76',plain,
    ( ( sk_B_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['71'])).

thf('77',plain,(
    ! [X12: $i] :
      ( v1_funct_1 @ ( sk_B_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('78',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I7wR4SFQte
% 0.15/0.36  % Computer   : n005.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:04:33 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 58 iterations in 0.027s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.22/0.50  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(t15_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ?[C:$i]:
% 0.22/0.50           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.22/0.50             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.50             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (((k1_relat_1 @ (sk_C_2 @ X14 @ X15)) = (X15))
% 0.22/0.50          | ((X15) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         ((v1_funct_1 @ (sk_C_2 @ X14 @ X15)) | ((X15) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf(t7_xboole_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.50          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf(d1_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X9 @ X8) | ((X9) = (X6)) | ((X8) != (k1_tarski @ X6)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X6 : $i, X9 : $i]:
% 0.22/0.50         (((X9) = (X6)) | ~ (r2_hidden @ X9 @ (k1_tarski @ X6)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.50          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X1 : $i, X3 : $i]:
% 0.22/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.50          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         (((k2_relat_1 @ (sk_C_2 @ X14 @ X15)) = (k1_tarski @ X14))
% 0.22/0.50          | ((X15) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf(t18_funct_1, conjecture,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50          ( ![C:$i]:
% 0.22/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.50                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i]:
% 0.22/0.50        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50             ( ![C:$i]:
% 0.22/0.50               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.50                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.22/0.50                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ X16))
% 0.22/0.50          | ~ (v1_funct_1 @ X16)
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.22/0.50          | ((X1) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.22/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_A) = (k1_xboole_0))
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0)))
% 0.22/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.50  thf('15', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_2) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf(t60_relat_1, axiom,
% 0.22/0.50    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.50     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.50  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B_2) = (k1_xboole_0)))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((((k2_relat_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ X16))
% 0.22/0.50          | ~ (v1_funct_1 @ X16)
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (((~ (r1_tarski @ sk_B_2 @ sk_A)
% 0.22/0.50         | ~ (v1_relat_1 @ sk_B_2)
% 0.22/0.50         | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.50         | ((sk_B_2) != (k1_relat_1 @ sk_B_2))))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('25', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((![X0 : $i]: (r1_tarski @ sk_B_2 @ X0))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((((k1_relat_1 @ sk_B_2) = (k1_xboole_0)))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      ((((k1_relat_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (((~ (v1_relat_1 @ sk_B_2)
% 0.22/0.50         | ~ (v1_funct_1 @ sk_B_2)
% 0.22/0.50         | ((sk_B_2) != (sk_B_2)))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '26', '31'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (((~ (v1_funct_1 @ sk_B_2) | ~ (v1_relat_1 @ sk_B_2)))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.50  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ?[B:$i]:
% 0.22/0.50       ( ( ![C:$i]:
% 0.22/0.50           ( ( r2_hidden @ C @ A ) =>
% 0.22/0.50             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.22/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.22/0.50  thf('34', plain, (![X12 : $i]: ((k1_relat_1 @ (sk_B_1 @ X12)) = (X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf(t64_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X11 : $i]:
% 0.22/0.50         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.22/0.50          | ((X11) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (((k1_relat_1 @ X0) != (sk_B_2))
% 0.22/0.50           | ~ (v1_relat_1 @ X0)
% 0.22/0.50           | ((X0) = (k1_xboole_0))))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (((k1_relat_1 @ X0) != (sk_B_2))
% 0.22/0.50           | ~ (v1_relat_1 @ X0)
% 0.22/0.50           | ((X0) = (sk_B_2))))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      ((![X0 : $i]:
% 0.22/0.50          (((X0) != (sk_B_2))
% 0.22/0.50           | ((sk_B_1 @ X0) = (sk_B_2))
% 0.22/0.50           | ~ (v1_relat_1 @ (sk_B_1 @ X0))))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['34', '39'])).
% 0.22/0.50  thf('41', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      ((![X0 : $i]: (((X0) != (sk_B_2)) | ((sk_B_1 @ X0) = (sk_B_2))))
% 0.22/0.50         <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      ((((sk_B_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.50  thf('44', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('45', plain, (((v1_relat_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('demod', [status(thm)], ['33', '45'])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      ((((sk_B_1 @ sk_B_2) = (sk_B_2))) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.50  thf('48', plain, (![X12 : $i]: (v1_funct_1 @ (sk_B_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('49', plain, (((v1_funct_1 @ sk_B_2)) <= ((((sk_B_2) = (k1_xboole_0))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf('50', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['46', '49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_2) = (k1_xboole_0)))),
% 0.22/0.50      inference('split', [status(esa)], ['15'])).
% 0.22/0.50  thf('52', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.22/0.50  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['16', '52'])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0)))
% 0.22/0.50          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['14', '53'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) = (k1_xboole_0))
% 0.22/0.50          | ((X0) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '54'])).
% 0.22/0.50  thf('56', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0)))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))
% 0.22/0.50          | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['55'])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (![X14 : $i, X15 : $i]:
% 0.22/0.50         ((v1_relat_1 @ (sk_C_2 @ X14 @ X15)) | ((X15) = (k1_xboole_0)))),
% 0.22/0.50      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) = (k1_xboole_0))
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ (sk_C_2 @ (sk_B @ sk_A) @ X0))))),
% 0.22/0.50      inference('clc', [status(thm)], ['56', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((sk_B_2) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '58'])).
% 0.22/0.50  thf('60', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.22/0.50  thf('61', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('62', plain,
% 0.22/0.50      (![X16 : $i]:
% 0.22/0.50         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 0.22/0.50          | ((sk_B_2) != (k1_relat_1 @ X16))
% 0.22/0.50          | ~ (v1_funct_1 @ X16)
% 0.22/0.50          | ~ (v1_relat_1 @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.22/0.50        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.50        | ((sk_B_2) != (k1_relat_1 @ k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.50  thf('64', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('65', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.50  thf('66', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.50        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.22/0.50        | ((sk_B_2) != (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.22/0.50  thf('67', plain, (![X12 : $i]: ((k1_relat_1 @ (sk_B_1 @ X12)) = (X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('68', plain,
% 0.22/0.50      (![X11 : $i]:
% 0.22/0.50         (((k1_relat_1 @ X11) != (k1_xboole_0))
% 0.22/0.50          | ((X11) = (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.50  thf('69', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (((X0) != (k1_xboole_0))
% 0.22/0.50          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.22/0.50          | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.50  thf('70', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('71', plain,
% 0.22/0.50      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B_1 @ X0) = (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.22/0.50  thf('72', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['71'])).
% 0.22/0.50  thf('73', plain, (![X12 : $i]: (v1_relat_1 @ (sk_B_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('74', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['72', '73'])).
% 0.22/0.50  thf('75', plain,
% 0.22/0.50      ((~ (v1_funct_1 @ k1_xboole_0) | ((sk_B_2) != (k1_xboole_0)))),
% 0.22/0.50      inference('demod', [status(thm)], ['66', '74'])).
% 0.22/0.50  thf('76', plain, (((sk_B_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.50      inference('simplify', [status(thm)], ['71'])).
% 0.22/0.50  thf('77', plain, (![X12 : $i]: (v1_funct_1 @ (sk_B_1 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.50  thf('78', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['76', '77'])).
% 0.22/0.50  thf('79', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.22/0.50      inference('demod', [status(thm)], ['75', '78'])).
% 0.22/0.50  thf('80', plain, ($false),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['60', '79'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
