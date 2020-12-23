%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YQjLe3WpAp

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:37 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 745 expanded)
%              Number of leaves         :   24 ( 214 expanded)
%              Depth                    :   25
%              Number of atoms          :  898 (7422 expanded)
%              Number of equality atoms :  154 (1303 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X18: $i,X19: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
        = X19 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('1',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_funct_1 @ ( sk_C_3 @ X18 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
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
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( X11 = X8 )
      | ( X10
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('5',plain,(
    ! [X8: $i,X11: $i] :
      ( ( X11 = X8 )
      | ~ ( r2_hidden @ X11 @ ( k1_tarski @ X8 ) ) ) ),
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

thf('12',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X0 @ X1 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

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

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( X13 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2 @ X0 @ sk_B_1 )
        = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2 @ X0 @ sk_B_1 )
        = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C @ X1 @ sk_B_1 ) )
          = X0 )
        | ( r1_tarski @ sk_B_1 @ X1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C @ X1 @ sk_B_1 ) )
          = X0 )
        | ( r1_tarski @ sk_B_1 @ X1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('34',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( X0 = X1 )
        | ( r1_tarski @ sk_B_1 @ X2 )
        | ( r1_tarski @ sk_B_1 @ X2 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r1_tarski @ sk_B_1 @ X2 )
        | ( X0 = X1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('37',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('44',plain,
    ( ( ( sk_B_1 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = k1_xboole_0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('46',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('47',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('48',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('49',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('52',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( ( k2_relat_1 @ sk_B_1 )
        = sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45','50','51'])).

thf('53',plain,
    ( ( ( k2_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( sk_B_1
       != ( k1_relat_1 @ sk_B_1 ) ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_relat_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('57',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('58',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('60',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( v1_funct_1 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,
    ( ( ( k1_relat_1 @ sk_B_1 )
      = sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('63',plain,
    ( ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
      | ( sk_B_1 != sk_B_1 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','61','62'])).

thf('64',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_A )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['63'])).

thf('67',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_B_1 @ X0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['18','67'])).

thf('69',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('70',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['68','69'])).

thf('71',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['14','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_relat_1 @ ( sk_C_3 @ X18 @ X19 ) )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B_1
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_B @ sk_A ) @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','76'])).

thf('78',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('80',plain,(
    ! [X14: $i] :
      ( ( ( k1_relat_1 @ X14 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('81',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ sk_A )
      | ( sk_B_1
       != ( k1_relat_1 @ X20 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B_1
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['47','48'])).

thf('88',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['58','59'])).

thf('89',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['37','38'])).

thf('90',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','87','88','89'])).

thf('91',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['16','70'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A != X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(demod,[status(thm)],['90','99'])).

thf('101',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['78','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YQjLe3WpAp
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 173 iterations in 0.156s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(t15_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ?[C:$i]:
% 0.42/0.62           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.42/0.62             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.42/0.62             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (((k1_relat_1 @ (sk_C_3 @ X18 @ X19)) = (X19))
% 0.42/0.62          | ((X19) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         ((v1_funct_1 @ (sk_C_3 @ X18 @ X19)) | ((X19) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.42/0.62  thf(t7_xboole_0, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.42/0.62          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.42/0.62  thf('2', plain,
% 0.42/0.62      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.42/0.62      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.42/0.62  thf(d3_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf(d1_tarski, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.42/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X11 @ X10)
% 0.42/0.62          | ((X11) = (X8))
% 0.42/0.62          | ((X10) != (k1_tarski @ X8)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d1_tarski])).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X8 : $i, X11 : $i]:
% 0.42/0.62         (((X11) = (X8)) | ~ (r2_hidden @ X11 @ (k1_tarski @ X8)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.42/0.62          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '5'])).
% 0.42/0.62  thf('7', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.42/0.62          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.42/0.62          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['6', '7'])).
% 0.42/0.62  thf('9', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.62      inference('simplify', [status(thm)], ['8'])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['2', '9'])).
% 0.42/0.62  thf('11', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         (((k2_relat_1 @ (sk_C_3 @ X18 @ X19)) = (k1_tarski @ X18))
% 0.42/0.62          | ((X19) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.42/0.62  thf(t18_funct_1, conjecture,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.62          ( ![C:$i]:
% 0.42/0.62            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.42/0.62                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i]:
% 0.42/0.62        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.62             ( ![C:$i]:
% 0.42/0.62               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.42/0.62                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.42/0.62                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.42/0.62  thf('12', plain,
% 0.42/0.62      (![X20 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ X20))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.42/0.62          | ((X1) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ (sk_C_3 @ X0 @ X1))
% 0.42/0.62          | ~ (v1_funct_1 @ (sk_C_3 @ X0 @ X1))
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ X0 @ X1))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.42/0.62  thf('14', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((sk_A) = (k1_xboole_0))
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0)))
% 0.42/0.62          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))
% 0.42/0.62          | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['10', '13'])).
% 0.42/0.62  thf('15', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('16', plain,
% 0.42/0.62      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf(d10_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.62  thf('18', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.42/0.62      inference('simplify', [status(thm)], ['17'])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ?[C:$i]:
% 0.42/0.62       ( ( ![D:$i]:
% 0.42/0.62           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.42/0.62         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.42/0.62         ( v1_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.42/0.62  thf(t64_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf('21', plain,
% 0.42/0.62      (![X13 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 0.42/0.62          | ((X13) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X0) != (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.42/0.62          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['22', '23'])).
% 0.42/0.62  thf('25', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((![X0 : $i]: ((sk_C_2 @ X0 @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['19', '25'])).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('28', plain,
% 0.42/0.62      ((![X0 : $i]: ((sk_C_2 @ X0 @ sk_B_1) = (sk_B_1)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain,
% 0.42/0.62      (![X1 : $i, X3 : $i]:
% 0.42/0.62         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.42/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.42/0.62         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 0.42/0.62          | ~ (r2_hidden @ X17 @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.42/0.62  thf('31', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1)
% 0.42/0.62          | ((k1_funct_1 @ (sk_C_2 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i]:
% 0.42/0.62          (((k1_funct_1 @ sk_B_1 @ (sk_C @ X1 @ sk_B_1)) = (X0))
% 0.42/0.62           | (r1_tarski @ sk_B_1 @ X1)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['28', '31'])).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i]:
% 0.42/0.62          (((k1_funct_1 @ sk_B_1 @ (sk_C @ X1 @ sk_B_1)) = (X0))
% 0.42/0.62           | (r1_tarski @ sk_B_1 @ X1)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['28', '31'])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62          (((X0) = (X1))
% 0.42/0.62           | (r1_tarski @ sk_B_1 @ X2)
% 0.42/0.62           | (r1_tarski @ sk_B_1 @ X2)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['32', '33'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62          ((r1_tarski @ sk_B_1 @ X2) | ((X0) = (X1))))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('37', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.42/0.62  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.42/0.62  thf('40', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_B_1) = (k1_xboole_0)))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['36', '39'])).
% 0.42/0.62  thf('41', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.42/0.62  thf(t65_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.42/0.62         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.42/0.62          | ((k2_relat_1 @ X14) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (((((sk_B_1) != (k1_xboole_0))
% 0.42/0.62         | ~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62         | ((k2_relat_1 @ sk_B_1) = (k1_xboole_0))))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('47', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.42/0.62  thf('49', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('50', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['46', '49'])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (((((sk_B_1) != (sk_B_1)) | ((k2_relat_1 @ sk_B_1) = (sk_B_1))))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['44', '45', '50', '51'])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['52'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      (![X20 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ X20))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (((~ (r1_tarski @ sk_B_1 @ sk_A)
% 0.42/0.62         | ~ (v1_relat_1 @ sk_B_1)
% 0.42/0.62         | ~ (v1_funct_1 @ sk_B_1)
% 0.42/0.62         | ((sk_B_1) != (k1_relat_1 @ sk_B_1))))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['53', '54'])).
% 0.42/0.62  thf('56', plain, (((v1_relat_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['46', '49'])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('58', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.62  thf('59', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.42/0.62      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.42/0.62  thf('60', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.42/0.62  thf('61', plain, (((v1_funct_1 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup+', [status(thm)], ['57', '60'])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      ((((k1_relat_1 @ sk_B_1) = (sk_B_1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.42/0.62  thf('63', plain,
% 0.42/0.62      (((~ (r1_tarski @ sk_B_1 @ sk_A) | ((sk_B_1) != (sk_B_1))))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('demod', [status(thm)], ['55', '56', '61', '62'])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      ((~ (r1_tarski @ sk_B_1 @ sk_A)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['63'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '64'])).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      ((~ (r1_tarski @ sk_B_1 @ sk_A)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('simplify', [status(thm)], ['63'])).
% 0.42/0.62  thf('67', plain,
% 0.42/0.62      ((![X0 : $i]: ~ (r1_tarski @ sk_B_1 @ X0))
% 0.42/0.62         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.42/0.62  thf('68', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['18', '67'])).
% 0.42/0.62  thf('69', plain,
% 0.42/0.62      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.42/0.62      inference('split', [status(esa)], ['15'])).
% 0.42/0.62  thf('70', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.42/0.62      inference('sat_resolution*', [status(thm)], ['68', '69'])).
% 0.42/0.62  thf('71', plain, (((sk_A) != (k1_xboole_0))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['16', '70'])).
% 0.42/0.62  thf('72', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0)))
% 0.42/0.62          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))
% 0.42/0.62          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))
% 0.42/0.62          | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['14', '71'])).
% 0.42/0.62  thf('73', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0))
% 0.42/0.62          | ((X0) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['1', '72'])).
% 0.42/0.62  thf('74', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0)))
% 0.42/0.62          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))
% 0.42/0.62          | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['73'])).
% 0.42/0.62  thf('75', plain,
% 0.42/0.62      (![X18 : $i, X19 : $i]:
% 0.42/0.62         ((v1_relat_1 @ (sk_C_3 @ X18 @ X19)) | ((X19) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.42/0.62  thf('76', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((X0) = (k1_xboole_0))
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ (sk_C_3 @ (sk_B @ sk_A) @ X0))))),
% 0.42/0.62      inference('clc', [status(thm)], ['74', '75'])).
% 0.42/0.62  thf('77', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((sk_B_1) != (X0)) | ((X0) = (k1_xboole_0)) | ((X0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '76'])).
% 0.42/0.62  thf('78', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['77'])).
% 0.42/0.62  thf('79', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.42/0.62  thf('80', plain,
% 0.42/0.62      (![X14 : $i]:
% 0.42/0.62         (((k1_relat_1 @ X14) != (k1_xboole_0))
% 0.42/0.62          | ((k2_relat_1 @ X14) = (k1_xboole_0))
% 0.42/0.62          | ~ (v1_relat_1 @ X14))),
% 0.42/0.62      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.42/0.62  thf('81', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.62        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['79', '80'])).
% 0.42/0.62  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('83', plain,
% 0.42/0.62      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.62        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['81', '82'])).
% 0.42/0.62  thf('84', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['83'])).
% 0.42/0.62  thf('85', plain,
% 0.42/0.62      (![X20 : $i]:
% 0.42/0.62         (~ (r1_tarski @ (k2_relat_1 @ X20) @ sk_A)
% 0.42/0.62          | ((sk_B_1) != (k1_relat_1 @ X20))
% 0.42/0.62          | ~ (v1_funct_1 @ X20)
% 0.42/0.62          | ~ (v1_relat_1 @ X20))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('86', plain,
% 0.42/0.62      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.42/0.62        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.42/0.62        | ~ (v1_funct_1 @ k1_xboole_0)
% 0.42/0.62        | ((sk_B_1) != (k1_relat_1 @ k1_xboole_0)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['84', '85'])).
% 0.42/0.62  thf('87', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup+', [status(thm)], ['47', '48'])).
% 0.42/0.62  thf('88', plain, ((v1_funct_1 @ k1_xboole_0)),
% 0.42/0.62      inference('sup+', [status(thm)], ['58', '59'])).
% 0.42/0.62  thf('89', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.42/0.62  thf('90', plain,
% 0.42/0.62      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B_1) != (k1_xboole_0)))),
% 0.42/0.62      inference('demod', [status(thm)], ['86', '87', '88', '89'])).
% 0.42/0.62  thf('91', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.42/0.62      inference('simplify', [status(thm)], ['24'])).
% 0.42/0.62  thf('92', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1)
% 0.42/0.62          | ((k1_funct_1 @ (sk_C_2 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '30'])).
% 0.42/0.62  thf('93', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 0.42/0.62          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.42/0.62      inference('sup+', [status(thm)], ['91', '92'])).
% 0.42/0.62  thf('94', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 0.42/0.62          | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.42/0.62      inference('sup+', [status(thm)], ['91', '92'])).
% 0.42/0.62  thf('95', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         (((X0) = (X1))
% 0.42/0.62          | (r1_tarski @ k1_xboole_0 @ X2)
% 0.42/0.62          | (r1_tarski @ k1_xboole_0 @ X2))),
% 0.42/0.62      inference('sup+', [status(thm)], ['93', '94'])).
% 0.42/0.62  thf('96', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['95'])).
% 0.42/0.62  thf('97', plain, (((sk_A) != (k1_xboole_0))),
% 0.42/0.62      inference('simpl_trail', [status(thm)], ['16', '70'])).
% 0.42/0.62  thf('98', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]: (((sk_A) != (X0)) | (r1_tarski @ k1_xboole_0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['96', '97'])).
% 0.42/0.62  thf('99', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.42/0.62      inference('simplify', [status(thm)], ['98'])).
% 0.42/0.62  thf('100', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.42/0.62      inference('demod', [status(thm)], ['90', '99'])).
% 0.42/0.62  thf('101', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['78', '100'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
