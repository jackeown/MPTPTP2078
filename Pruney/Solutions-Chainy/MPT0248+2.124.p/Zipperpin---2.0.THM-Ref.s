%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhxMgikajn

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:36 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 416 expanded)
%              Number of leaves         :   27 ( 119 expanded)
%              Depth                    :   26
%              Number of atoms          :  821 (5258 expanded)
%              Number of equality atoms :  130 (1112 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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

thf('5',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('10',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('14',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50
        = ( k1_tarski @ X49 ) )
      | ( X50 = k1_xboole_0 )
      | ~ ( r1_tarski @ X50 @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['5'])).

thf('26',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['9','11','27'])).

thf('29',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['8','28'])).

thf('30',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('34',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('35',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X52: $i,X53: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X52 @ X53 ) )
      = ( k2_xboole_0 @ X52 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['38','44'])).

thf('46',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(simplify,[status(thm)],['50'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('53',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X54: $i,X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X54 @ X56 ) @ X57 )
      | ~ ( r2_hidden @ X56 @ X57 )
      | ~ ( r2_hidden @ X54 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ ( k3_tarski @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ ( k3_tarski @ sk_B_1 ) @ ( k3_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X19: $i] :
      ( ( k2_tarski @ X19 @ X19 )
      = ( k1_tarski @ X19 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('67',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('71',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X12 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('72',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('78',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('80',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['73','80'])).

thf('82',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['72','81'])).

thf('83',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('84',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['8','28'])).

thf('86',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(demod,[status(thm)],['32','86'])).

thf('88',plain,(
    $false ),
    inference(demod,[status(thm)],['31','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uhxMgikajn
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:13:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.21/3.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.21/3.41  % Solved by: fo/fo7.sh
% 3.21/3.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.41  % done 8474 iterations in 2.934s
% 3.21/3.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.21/3.41  % SZS output start Refutation
% 3.21/3.41  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.21/3.41  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.21/3.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.21/3.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.21/3.41  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.21/3.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.21/3.41  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.21/3.41  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.21/3.41  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.41  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.21/3.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.21/3.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.21/3.41  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.21/3.41  thf(d3_tarski, axiom,
% 3.21/3.41    (![A:$i,B:$i]:
% 3.21/3.41     ( ( r1_tarski @ A @ B ) <=>
% 3.21/3.41       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.21/3.41  thf('0', plain,
% 3.21/3.41      (![X4 : $i, X6 : $i]:
% 3.21/3.41         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.21/3.41      inference('cnf', [status(esa)], [d3_tarski])).
% 3.21/3.41  thf(d1_xboole_0, axiom,
% 3.21/3.41    (![A:$i]:
% 3.21/3.41     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.21/3.41  thf('1', plain,
% 3.21/3.41      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.21/3.41      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.21/3.41  thf('2', plain,
% 3.21/3.41      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.41      inference('sup-', [status(thm)], ['0', '1'])).
% 3.21/3.41  thf(t12_xboole_1, axiom,
% 3.21/3.41    (![A:$i,B:$i]:
% 3.21/3.41     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.21/3.41  thf('3', plain,
% 3.21/3.41      (![X9 : $i, X10 : $i]:
% 3.21/3.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 3.21/3.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.21/3.41  thf('4', plain,
% 3.21/3.41      (![X0 : $i, X1 : $i]:
% 3.21/3.41         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['2', '3'])).
% 3.21/3.41  thf(t43_zfmisc_1, conjecture,
% 3.21/3.41    (![A:$i,B:$i,C:$i]:
% 3.21/3.41     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.21/3.41          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.21/3.41          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.21/3.41          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 3.21/3.41  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.41    (~( ![A:$i,B:$i,C:$i]:
% 3.21/3.41        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 3.21/3.41             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.21/3.41             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 3.21/3.41             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 3.21/3.41    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 3.21/3.41  thf('5', plain,
% 3.21/3.41      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('6', plain,
% 3.21/3.41      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 3.21/3.41         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('split', [status(esa)], ['5'])).
% 3.21/3.41  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('8', plain,
% 3.21/3.41      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 3.21/3.41         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.41  thf('9', plain,
% 3.21/3.41      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('split', [status(esa)], ['5'])).
% 3.21/3.41  thf('10', plain,
% 3.21/3.41      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('11', plain,
% 3.21/3.41      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 3.21/3.41       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('split', [status(esa)], ['10'])).
% 3.21/3.41  thf(t7_xboole_1, axiom,
% 3.21/3.41    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.21/3.41  thf('12', plain,
% 3.21/3.41      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 3.21/3.41      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.21/3.41  thf('13', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf(l3_zfmisc_1, axiom,
% 3.21/3.41    (![A:$i,B:$i]:
% 3.21/3.41     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 3.21/3.41       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 3.21/3.41  thf('14', plain,
% 3.21/3.41      (![X49 : $i, X50 : $i]:
% 3.21/3.41         (((X50) = (k1_tarski @ X49))
% 3.21/3.41          | ((X50) = (k1_xboole_0))
% 3.21/3.41          | ~ (r1_tarski @ X50 @ (k1_tarski @ X49)))),
% 3.21/3.41      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 3.21/3.41  thf('15', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41          | ((X0) = (k1_xboole_0))
% 3.21/3.41          | ((X0) = (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['13', '14'])).
% 3.21/3.41  thf('16', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('17', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41          | ((X0) = (k1_xboole_0))
% 3.21/3.41          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 3.21/3.41      inference('demod', [status(thm)], ['15', '16'])).
% 3.21/3.41  thf('18', plain,
% 3.21/3.41      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['12', '17'])).
% 3.21/3.41  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('20', plain,
% 3.21/3.41      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('21', plain,
% 3.21/3.41      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 3.21/3.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('split', [status(esa)], ['20'])).
% 3.21/3.41  thf('22', plain,
% 3.21/3.41      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 3.21/3.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('sup-', [status(thm)], ['19', '21'])).
% 3.21/3.41  thf('23', plain,
% 3.21/3.41      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 3.21/3.41         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('sup-', [status(thm)], ['18', '22'])).
% 3.21/3.41  thf('24', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('simplify', [status(thm)], ['23'])).
% 3.21/3.41  thf('25', plain,
% 3.21/3.41      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 3.21/3.41      inference('split', [status(esa)], ['5'])).
% 3.21/3.41  thf('26', plain,
% 3.21/3.41      ((((sk_B_1) != (sk_B_1)))
% 3.21/3.41         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 3.21/3.41             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('sup-', [status(thm)], ['24', '25'])).
% 3.21/3.41  thf('27', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('simplify', [status(thm)], ['26'])).
% 3.21/3.41  thf('28', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('sat_resolution*', [status(thm)], ['9', '11', '27'])).
% 3.21/3.41  thf('29', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('simpl_trail', [status(thm)], ['8', '28'])).
% 3.21/3.41  thf('30', plain, ((((sk_C_1) != (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 3.21/3.41      inference('sup-', [status(thm)], ['4', '29'])).
% 3.21/3.41  thf('31', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.21/3.41      inference('simplify', [status(thm)], ['30'])).
% 3.21/3.41  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.21/3.41  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.41  thf('33', plain,
% 3.21/3.41      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['12', '17'])).
% 3.21/3.41  thf('34', plain,
% 3.21/3.41      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['12', '17'])).
% 3.21/3.41  thf('35', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf(t69_enumset1, axiom,
% 3.21/3.41    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.21/3.41  thf('36', plain,
% 3.21/3.41      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.41      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.41  thf(l51_zfmisc_1, axiom,
% 3.21/3.41    (![A:$i,B:$i]:
% 3.21/3.41     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.21/3.41  thf('37', plain,
% 3.21/3.41      (![X52 : $i, X53 : $i]:
% 3.21/3.41         ((k3_tarski @ (k2_tarski @ X52 @ X53)) = (k2_xboole_0 @ X52 @ X53))),
% 3.21/3.41      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.21/3.41  thf('38', plain,
% 3.21/3.41      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 3.21/3.41      inference('sup+', [status(thm)], ['36', '37'])).
% 3.21/3.41  thf('39', plain,
% 3.21/3.41      (![X4 : $i, X6 : $i]:
% 3.21/3.41         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.21/3.41      inference('cnf', [status(esa)], [d3_tarski])).
% 3.21/3.41  thf('40', plain,
% 3.21/3.41      (![X4 : $i, X6 : $i]:
% 3.21/3.41         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 3.21/3.41      inference('cnf', [status(esa)], [d3_tarski])).
% 3.21/3.41  thf('41', plain,
% 3.21/3.41      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 3.21/3.41      inference('sup-', [status(thm)], ['39', '40'])).
% 3.21/3.41  thf('42', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.21/3.41      inference('simplify', [status(thm)], ['41'])).
% 3.21/3.41  thf('43', plain,
% 3.21/3.41      (![X9 : $i, X10 : $i]:
% 3.21/3.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 3.21/3.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.21/3.41  thf('44', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.21/3.41      inference('sup-', [status(thm)], ['42', '43'])).
% 3.21/3.41  thf('45', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 3.21/3.41      inference('demod', [status(thm)], ['38', '44'])).
% 3.21/3.41  thf('46', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 3.21/3.41      inference('sup+', [status(thm)], ['35', '45'])).
% 3.21/3.41  thf('47', plain,
% 3.21/3.41      ((((k3_tarski @ sk_B_1) = (sk_A)) | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup+', [status(thm)], ['34', '46'])).
% 3.21/3.41  thf('48', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.41  thf('49', plain,
% 3.21/3.41      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup+', [status(thm)], ['47', '48'])).
% 3.21/3.41  thf('50', plain,
% 3.21/3.41      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup+', [status(thm)], ['33', '49'])).
% 3.21/3.41  thf('51', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))
% 3.21/3.41        | ((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))),
% 3.21/3.41      inference('simplify', [status(thm)], ['50'])).
% 3.21/3.41  thf('52', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))
% 3.21/3.41        | ((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))),
% 3.21/3.41      inference('simplify', [status(thm)], ['50'])).
% 3.21/3.41  thf(l27_zfmisc_1, axiom,
% 3.21/3.41    (![A:$i,B:$i]:
% 3.21/3.41     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.21/3.41  thf('53', plain,
% 3.21/3.41      (![X47 : $i, X48 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ (k1_tarski @ X47) @ X48) | (r2_hidden @ X47 @ X48))),
% 3.21/3.41      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 3.21/3.41  thf('54', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 3.21/3.41      inference('sup+', [status(thm)], ['52', '53'])).
% 3.21/3.41  thf('55', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 3.21/3.41      inference('sup+', [status(thm)], ['52', '53'])).
% 3.21/3.41  thf(t38_zfmisc_1, axiom,
% 3.21/3.41    (![A:$i,B:$i,C:$i]:
% 3.21/3.41     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 3.21/3.41       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 3.21/3.41  thf('56', plain,
% 3.21/3.41      (![X54 : $i, X56 : $i, X57 : $i]:
% 3.21/3.41         ((r1_tarski @ (k2_tarski @ X54 @ X56) @ X57)
% 3.21/3.41          | ~ (r2_hidden @ X56 @ X57)
% 3.21/3.41          | ~ (r2_hidden @ X54 @ X57))),
% 3.21/3.41      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.21/3.41  thf('57', plain,
% 3.21/3.41      (![X0 : $i, X1 : $i]:
% 3.21/3.41         (((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ~ (r2_hidden @ X1 @ X0)
% 3.21/3.41          | (r1_tarski @ (k2_tarski @ X1 @ (k3_tarski @ sk_B_1)) @ X0))),
% 3.21/3.41      inference('sup-', [status(thm)], ['55', '56'])).
% 3.21/3.41  thf('58', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         (((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | (r1_tarski @ 
% 3.21/3.41             (k2_tarski @ (k3_tarski @ sk_B_1) @ (k3_tarski @ sk_B_1)) @ X0)
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['54', '57'])).
% 3.21/3.41  thf('59', plain,
% 3.21/3.41      (![X19 : $i]: ((k2_tarski @ X19 @ X19) = (k1_tarski @ X19))),
% 3.21/3.41      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.21/3.41  thf('60', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         (((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0)
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('demod', [status(thm)], ['58', '59'])).
% 3.21/3.41  thf('61', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0)
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('simplify', [status(thm)], ['60'])).
% 3.21/3.41  thf('62', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_tarski @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_xboole_0 @ sk_B_1 @ X0))),
% 3.21/3.41      inference('sup+', [status(thm)], ['51', '61'])).
% 3.21/3.41  thf('63', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_tarski @ sk_B_1 @ X0))),
% 3.21/3.41      inference('simplify', [status(thm)], ['62'])).
% 3.21/3.41  thf(symmetry_r1_xboole_0, axiom,
% 3.21/3.41    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 3.21/3.41  thf('64', plain,
% 3.21/3.41      (![X7 : $i, X8 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 3.21/3.41      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 3.21/3.41  thf('65', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_tarski @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 3.21/3.41      inference('sup-', [status(thm)], ['63', '64'])).
% 3.21/3.41  thf('66', plain,
% 3.21/3.41      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 3.21/3.41        | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['12', '17'])).
% 3.21/3.41  thf(t70_xboole_1, axiom,
% 3.21/3.41    (![A:$i,B:$i,C:$i]:
% 3.21/3.41     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 3.21/3.41            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 3.21/3.41       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 3.21/3.41            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 3.21/3.41  thf('67', plain,
% 3.21/3.41      (![X13 : $i, X14 : $i, X16 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ X13 @ X16)
% 3.21/3.41          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 3.21/3.41      inference('cnf', [status(esa)], [t70_xboole_1])).
% 3.21/3.41  thf('68', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         (~ (r1_xboole_0 @ X0 @ sk_B_1)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 3.21/3.41      inference('sup-', [status(thm)], ['66', '67'])).
% 3.21/3.41  thf('69', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         (((sk_B_1) = (k1_xboole_0))
% 3.21/3.41          | (r1_tarski @ sk_B_1 @ X0)
% 3.21/3.41          | (r1_xboole_0 @ X0 @ sk_C_1)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['65', '68'])).
% 3.21/3.41  thf('70', plain,
% 3.21/3.41      (![X0 : $i]:
% 3.21/3.41         ((r1_xboole_0 @ X0 @ sk_C_1)
% 3.21/3.41          | (r1_tarski @ sk_B_1 @ X0)
% 3.21/3.41          | ((sk_B_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('simplify', [status(thm)], ['69'])).
% 3.21/3.41  thf(t66_xboole_1, axiom,
% 3.21/3.41    (![A:$i]:
% 3.21/3.41     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 3.21/3.41       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 3.21/3.41  thf('71', plain,
% 3.21/3.41      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X12 @ X12))),
% 3.21/3.41      inference('cnf', [status(esa)], [t66_xboole_1])).
% 3.21/3.41  thf('72', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))
% 3.21/3.41        | (r1_tarski @ sk_B_1 @ sk_C_1)
% 3.21/3.41        | ((sk_C_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['70', '71'])).
% 3.21/3.41  thf('73', plain,
% 3.21/3.41      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 3.21/3.41      inference('split', [status(esa)], ['20'])).
% 3.21/3.41  thf('74', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('simplify', [status(thm)], ['23'])).
% 3.21/3.41  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.41      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.41  thf('76', plain,
% 3.21/3.41      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 3.21/3.41      inference('sup+', [status(thm)], ['74', '75'])).
% 3.21/3.41  thf('77', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 3.21/3.41      inference('simplify', [status(thm)], ['30'])).
% 3.21/3.41  thf('78', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['76', '77'])).
% 3.21/3.41  thf('79', plain,
% 3.21/3.41      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 3.21/3.41      inference('split', [status(esa)], ['20'])).
% 3.21/3.41  thf('80', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 3.21/3.41      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 3.21/3.41  thf('81', plain, (((sk_C_1) != (k1_xboole_0))),
% 3.21/3.41      inference('simpl_trail', [status(thm)], ['73', '80'])).
% 3.21/3.41  thf('82', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0)) | (r1_tarski @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('simplify_reflect-', [status(thm)], ['72', '81'])).
% 3.21/3.41  thf('83', plain,
% 3.21/3.41      (![X9 : $i, X10 : $i]:
% 3.21/3.41         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 3.21/3.41      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.21/3.41  thf('84', plain,
% 3.21/3.41      ((((sk_B_1) = (k1_xboole_0))
% 3.21/3.41        | ((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1)))),
% 3.21/3.41      inference('sup-', [status(thm)], ['82', '83'])).
% 3.21/3.41  thf('85', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 3.21/3.41      inference('simpl_trail', [status(thm)], ['8', '28'])).
% 3.21/3.41  thf('86', plain, (((sk_B_1) = (k1_xboole_0))),
% 3.21/3.41      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 3.21/3.41  thf('87', plain, ((v1_xboole_0 @ sk_B_1)),
% 3.21/3.41      inference('demod', [status(thm)], ['32', '86'])).
% 3.21/3.41  thf('88', plain, ($false), inference('demod', [status(thm)], ['31', '87'])).
% 3.21/3.41  
% 3.21/3.41  % SZS output end Refutation
% 3.21/3.41  
% 3.21/3.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
