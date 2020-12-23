%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oRwWJPMftz

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:25 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 401 expanded)
%              Number of leaves         :   24 ( 121 expanded)
%              Depth                    :   22
%              Number of atoms          :  664 (4020 expanded)
%              Number of equality atoms :   91 ( 700 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t43_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B = k1_xboole_0 )
            & ( C
              = ( k1_tarski @ A ) ) )
        & ~ ( ( B
              = ( k1_tarski @ A ) )
            & ( C = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B = k1_xboole_0 )
              & ( C
                = ( k1_tarski @ A ) ) )
          & ~ ( ( B
                = ( k1_tarski @ A ) )
              & ( C = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_zfmisc_1])).

thf('0',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r1_tarski @ X13 @ X14 )
      | ( r1_tarski @ X13 @ ( k2_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k3_xboole_0 @ X6 @ X9 ) )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','16'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X50 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('22',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('28',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['29'])).

thf('31',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('32',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X53: $i,X54: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X53 ) @ X54 )
      | ( r2_hidden @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_tarski @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('38',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X50: $i,X52: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X50 ) @ X52 )
      | ~ ( r2_hidden @ X50 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('48',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('54',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['29'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['31','33','58'])).

thf('60',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','59'])).

thf('61',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['28','60'])).

thf('62',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['19','61'])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('64',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','64'])).

thf('66',plain,
    ( $false
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(clc,[status(thm)],['19','61'])).

thf('68',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k1_tarski @ sk_A )
      = ( k2_xboole_0 @ k1_xboole_0 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_A )
          = ( k2_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['71','74'])).

thf('76',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = sk_C_1 )
      | ~ ( v1_xboole_0 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['70','75'])).

thf('77',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['30','59'])).

thf('78',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf('80',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('81',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['66','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oRwWJPMftz
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.36/1.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.36/1.60  % Solved by: fo/fo7.sh
% 1.36/1.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.60  % done 3461 iterations in 1.148s
% 1.36/1.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.36/1.60  % SZS output start Refutation
% 1.36/1.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.36/1.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.60  thf(sk_B_type, type, sk_B: $i > $i).
% 1.36/1.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.36/1.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.36/1.60  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.36/1.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.36/1.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.36/1.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.60  thf(t43_zfmisc_1, conjecture,
% 1.36/1.60    (![A:$i,B:$i,C:$i]:
% 1.36/1.60     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.36/1.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.36/1.60          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.36/1.60          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.36/1.60  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.60    (~( ![A:$i,B:$i,C:$i]:
% 1.36/1.60        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.36/1.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.36/1.60             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.36/1.60             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.36/1.60    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.36/1.60  thf('0', plain,
% 1.36/1.60      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('1', plain,
% 1.36/1.60      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.36/1.60      inference('split', [status(esa)], ['0'])).
% 1.36/1.60  thf(d1_xboole_0, axiom,
% 1.36/1.60    (![A:$i]:
% 1.36/1.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.36/1.60  thf('2', plain,
% 1.36/1.60      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.36/1.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.60  thf(l27_zfmisc_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.36/1.60  thf('3', plain,
% 1.36/1.60      (![X53 : $i, X54 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 1.36/1.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.36/1.60  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf(d10_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.36/1.60  thf('5', plain,
% 1.36/1.60      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 1.36/1.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.60  thf('6', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.36/1.60      inference('simplify', [status(thm)], ['5'])).
% 1.36/1.60  thf(t10_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i,C:$i]:
% 1.36/1.60     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.36/1.60  thf('7', plain,
% 1.36/1.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.36/1.60         (~ (r1_tarski @ X13 @ X14)
% 1.36/1.60          | (r1_tarski @ X13 @ (k2_xboole_0 @ X15 @ X14)))),
% 1.36/1.60      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.36/1.60  thf('8', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['6', '7'])).
% 1.36/1.60  thf('9', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 1.36/1.60      inference('sup+', [status(thm)], ['4', '8'])).
% 1.36/1.60  thf(t28_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.36/1.60  thf('10', plain,
% 1.36/1.60      (![X18 : $i, X19 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.36/1.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.36/1.60  thf('11', plain, (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_C_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['9', '10'])).
% 1.36/1.60  thf(commutativity_k3_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.36/1.60  thf('12', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.36/1.60  thf(t4_xboole_0, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.60            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.36/1.60       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.36/1.60            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.36/1.60  thf('13', plain,
% 1.36/1.60      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X8 @ (k3_xboole_0 @ X6 @ X9))
% 1.36/1.60          | ~ (r1_xboole_0 @ X6 @ X9))),
% 1.36/1.60      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.36/1.60  thf('14', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.36/1.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['12', '13'])).
% 1.36/1.60  thf('15', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X0 @ sk_C_1)
% 1.36/1.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['11', '14'])).
% 1.36/1.60  thf('16', plain,
% 1.36/1.60      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['3', '15'])).
% 1.36/1.60  thf('17', plain, (((v1_xboole_0 @ sk_C_1) | (r2_hidden @ sk_A @ sk_C_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['2', '16'])).
% 1.36/1.60  thf(l1_zfmisc_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.36/1.60  thf('18', plain,
% 1.36/1.60      (![X50 : $i, X52 : $i]:
% 1.36/1.60         ((r1_tarski @ (k1_tarski @ X50) @ X52) | ~ (r2_hidden @ X50 @ X52))),
% 1.36/1.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.36/1.60  thf('19', plain,
% 1.36/1.60      (((v1_xboole_0 @ sk_C_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['17', '18'])).
% 1.36/1.60  thf('20', plain, ((r1_tarski @ sk_C_1 @ (k1_tarski @ sk_A))),
% 1.36/1.60      inference('sup+', [status(thm)], ['4', '8'])).
% 1.36/1.60  thf(t12_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]:
% 1.36/1.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.36/1.60  thf('21', plain,
% 1.36/1.60      (![X16 : $i, X17 : $i]:
% 1.36/1.60         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.36/1.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.36/1.60  thf('22', plain,
% 1.36/1.60      (((k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.36/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.36/1.60  thf(t7_xboole_1, axiom,
% 1.36/1.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.36/1.60  thf('23', plain,
% 1.36/1.60      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.36/1.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.36/1.60  thf('24', plain,
% 1.36/1.60      (![X10 : $i, X12 : $i]:
% 1.36/1.60         (((X10) = (X12))
% 1.36/1.60          | ~ (r1_tarski @ X12 @ X10)
% 1.36/1.60          | ~ (r1_tarski @ X10 @ X12))),
% 1.36/1.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.60  thf('25', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i]:
% 1.36/1.60         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.36/1.60          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['23', '24'])).
% 1.36/1.60  thf('26', plain,
% 1.36/1.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 1.36/1.60        | ((k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (sk_C_1)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['22', '25'])).
% 1.36/1.60  thf('27', plain,
% 1.36/1.60      (((k2_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.36/1.60      inference('sup-', [status(thm)], ['20', '21'])).
% 1.36/1.60  thf('28', plain,
% 1.36/1.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)
% 1.36/1.60        | ((k1_tarski @ sk_A) = (sk_C_1)))),
% 1.36/1.60      inference('demod', [status(thm)], ['26', '27'])).
% 1.36/1.60  thf('29', plain,
% 1.36/1.60      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('30', plain,
% 1.36/1.60      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.36/1.60         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('split', [status(esa)], ['29'])).
% 1.36/1.60  thf('31', plain,
% 1.36/1.60      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.36/1.60      inference('split', [status(esa)], ['29'])).
% 1.36/1.60  thf('32', plain,
% 1.36/1.60      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('33', plain,
% 1.36/1.60      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.36/1.60       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('split', [status(esa)], ['32'])).
% 1.36/1.60  thf('34', plain,
% 1.36/1.60      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.36/1.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.60  thf('35', plain,
% 1.36/1.60      (![X53 : $i, X54 : $i]:
% 1.36/1.60         ((r1_xboole_0 @ (k1_tarski @ X53) @ X54) | (r2_hidden @ X53 @ X54))),
% 1.36/1.60      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.36/1.60  thf('36', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('37', plain,
% 1.36/1.60      (![X20 : $i, X21 : $i]: (r1_tarski @ X20 @ (k2_xboole_0 @ X20 @ X21))),
% 1.36/1.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.36/1.60  thf('38', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.36/1.60      inference('sup+', [status(thm)], ['36', '37'])).
% 1.36/1.60  thf('39', plain,
% 1.36/1.60      (![X18 : $i, X19 : $i]:
% 1.36/1.60         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 1.36/1.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.36/1.60  thf('40', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['38', '39'])).
% 1.36/1.60  thf('41', plain,
% 1.36/1.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.36/1.60          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['12', '13'])).
% 1.36/1.60  thf('42', plain,
% 1.36/1.60      (![X0 : $i]:
% 1.36/1.60         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.36/1.60          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['40', '41'])).
% 1.36/1.60  thf('43', plain,
% 1.36/1.60      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['35', '42'])).
% 1.36/1.60  thf('44', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['34', '43'])).
% 1.36/1.60  thf('45', plain,
% 1.36/1.60      (![X50 : $i, X52 : $i]:
% 1.36/1.60         ((r1_tarski @ (k1_tarski @ X50) @ X52) | ~ (r2_hidden @ X50 @ X52))),
% 1.36/1.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.36/1.60  thf('46', plain,
% 1.36/1.60      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.36/1.60      inference('sup-', [status(thm)], ['44', '45'])).
% 1.36/1.60  thf('47', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.36/1.60      inference('sup+', [status(thm)], ['36', '37'])).
% 1.36/1.60  thf('48', plain,
% 1.36/1.60      (![X10 : $i, X12 : $i]:
% 1.36/1.60         (((X10) = (X12))
% 1.36/1.60          | ~ (r1_tarski @ X12 @ X10)
% 1.36/1.60          | ~ (r1_tarski @ X10 @ X12))),
% 1.36/1.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.60  thf('49', plain,
% 1.36/1.60      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.36/1.60        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['47', '48'])).
% 1.36/1.60  thf('50', plain,
% 1.36/1.60      (((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['46', '49'])).
% 1.36/1.60  thf('51', plain,
% 1.36/1.60      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.36/1.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('split', [status(esa)], ['0'])).
% 1.36/1.60  thf('52', plain,
% 1.36/1.60      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 1.36/1.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup-', [status(thm)], ['50', '51'])).
% 1.36/1.60  thf('53', plain,
% 1.36/1.60      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('simplify', [status(thm)], ['52'])).
% 1.36/1.60  thf(l13_xboole_0, axiom,
% 1.36/1.60    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.36/1.60  thf('54', plain,
% 1.36/1.60      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.36/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.60  thf('55', plain,
% 1.36/1.60      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.36/1.60  thf('56', plain,
% 1.36/1.60      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.36/1.60      inference('split', [status(esa)], ['29'])).
% 1.36/1.60  thf('57', plain,
% 1.36/1.60      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.36/1.60         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 1.36/1.60             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup-', [status(thm)], ['55', '56'])).
% 1.36/1.60  thf('58', plain,
% 1.36/1.60      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('simplify', [status(thm)], ['57'])).
% 1.36/1.60  thf('59', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('sat_resolution*', [status(thm)], ['31', '33', '58'])).
% 1.36/1.60  thf('60', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.36/1.60      inference('simpl_trail', [status(thm)], ['30', '59'])).
% 1.36/1.60  thf('61', plain, (~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1)),
% 1.36/1.60      inference('simplify_reflect-', [status(thm)], ['28', '60'])).
% 1.36/1.60  thf('62', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.36/1.60      inference('clc', [status(thm)], ['19', '61'])).
% 1.36/1.60  thf('63', plain,
% 1.36/1.60      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.36/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.60  thf('64', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['62', '63'])).
% 1.36/1.60  thf('65', plain,
% 1.36/1.60      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.36/1.60      inference('demod', [status(thm)], ['1', '64'])).
% 1.36/1.60  thf('66', plain, (($false) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.36/1.60      inference('simplify', [status(thm)], ['65'])).
% 1.36/1.60  thf('67', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.36/1.60      inference('clc', [status(thm)], ['19', '61'])).
% 1.36/1.60  thf('68', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 1.36/1.60      inference('simplify', [status(thm)], ['5'])).
% 1.36/1.60  thf('69', plain,
% 1.36/1.60      (![X16 : $i, X17 : $i]:
% 1.36/1.60         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 1.36/1.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.36/1.60  thf('70', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.36/1.60      inference('sup-', [status(thm)], ['68', '69'])).
% 1.36/1.60  thf('71', plain,
% 1.36/1.60      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.36/1.60      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.60  thf('72', plain,
% 1.36/1.60      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup-', [status(thm)], ['53', '54'])).
% 1.36/1.60  thf('73', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.36/1.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.60  thf('74', plain,
% 1.36/1.60      ((((k1_tarski @ sk_A) = (k2_xboole_0 @ k1_xboole_0 @ sk_C_1)))
% 1.36/1.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup+', [status(thm)], ['72', '73'])).
% 1.36/1.60  thf('75', plain,
% 1.36/1.60      ((![X0 : $i]:
% 1.36/1.60          (((k1_tarski @ sk_A) = (k2_xboole_0 @ X0 @ sk_C_1))
% 1.36/1.60           | ~ (v1_xboole_0 @ X0)))
% 1.36/1.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup+', [status(thm)], ['71', '74'])).
% 1.36/1.60  thf('76', plain,
% 1.36/1.60      (((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_C_1)))
% 1.36/1.60         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('sup+', [status(thm)], ['70', '75'])).
% 1.36/1.60  thf('77', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.36/1.60      inference('simpl_trail', [status(thm)], ['30', '59'])).
% 1.36/1.60  thf('78', plain,
% 1.36/1.60      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.36/1.60      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 1.36/1.60  thf('79', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('sup-', [status(thm)], ['67', '78'])).
% 1.36/1.60  thf('80', plain,
% 1.36/1.60      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.36/1.60      inference('split', [status(esa)], ['0'])).
% 1.36/1.60  thf('81', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.36/1.60      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 1.36/1.60  thf('82', plain, ($false),
% 1.36/1.60      inference('simpl_trail', [status(thm)], ['66', '81'])).
% 1.36/1.60  
% 1.36/1.60  % SZS output end Refutation
% 1.36/1.60  
% 1.36/1.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
