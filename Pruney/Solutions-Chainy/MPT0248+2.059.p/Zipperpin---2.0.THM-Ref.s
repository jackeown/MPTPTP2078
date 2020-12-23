%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FwNtIY21RH

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:26 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  177 (2601 expanded)
%              Number of leaves         :   35 ( 781 expanded)
%              Depth                    :   25
%              Number of atoms          : 1086 (28028 expanded)
%              Number of equality atoms :  161 (5082 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('1',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X49 ) @ X50 )
      | ( r2_hidden @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('18',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
        = ( k1_tarski @ X51 ) )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('26',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','36'])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( sk_C_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('46',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('52',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('53',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['44','50','51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['4','53'])).

thf('55',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('57',plain,(
    ! [X29: $i] :
      ( ( k3_xboole_0 @ X29 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('60',plain,(
    ! [X32: $i] :
      ( ( k5_xboole_0 @ X32 @ k1_xboole_0 )
      = X32 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ X19 @ ( k2_xboole_0 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
      = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['56','67'])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('70',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','50','51','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_C_1 @ sk_B_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ( ( k4_xboole_0 @ X14 @ X15 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('76',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('79',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B_1 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference(simplify,[status(thm)],['76'])).

thf('83',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('86',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('88',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k4_xboole_0 @ X35 @ X36 )
        = X35 )
      | ~ ( r1_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('91',plain,(
    ! [X33: $i,X34: $i] :
      ( r1_tarski @ X33 @ ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('92',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_xboole_0 @ X23 @ X22 )
        = X22 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_B_1 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['94','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['69','72'])).

thf('100',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['89','100','101'])).

thf('103',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('104',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('105',plain,(
    ! [X53: $i,X54: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X53 @ X54 ) )
      = ( k2_xboole_0 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('111',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['102','111'])).

thf('113',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k3_xboole_0 @ X52 @ ( k1_tarski @ X51 ) )
        = ( k1_tarski @ X51 ) )
      | ~ ( r2_hidden @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
        = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('117',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['109','110'])).

thf('119',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['117','118'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['114','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( ( k4_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_C_1 = sk_B_1 )
    | ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['86','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('126',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('127',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( sk_C_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['44','50','51','71'])).

thf('130',plain,(
    sk_C_1
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( sk_C_1 != sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['125','130'])).

thf('132',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['69','72'])).

thf('133',plain,(
    sk_C_1 != sk_B_1 ),
    inference(clc,[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X35: $i,X37: $i] :
      ( ( r1_xboole_0 @ X35 @ X37 )
      | ( ( k4_xboole_0 @ X35 @ X37 )
       != X35 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('136',plain,
    ( ( sk_B_1 != sk_B_1 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['81','137'])).

thf('139',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['55','138'])).

thf('140',plain,(
    $false ),
    inference(demod,[status(thm)],['54','139'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FwNtIY21RH
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:14:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 764 iterations in 0.257s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.73  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.51/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.73  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.51/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.73  thf(l13_xboole_0, axiom,
% 0.51/0.73    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.51/0.73  thf('0', plain,
% 0.51/0.73      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.51/0.73  thf(t43_zfmisc_1, conjecture,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.51/0.73          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.73          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.73          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.73        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.51/0.73             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.73             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.51/0.73             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('2', plain,
% 0.51/0.73      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.51/0.73      inference('split', [status(esa)], ['1'])).
% 0.51/0.73  thf('3', plain,
% 0.51/0.73      ((![X0 : $i]: (((sk_C_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.51/0.73         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['0', '2'])).
% 0.51/0.73  thf('4', plain,
% 0.51/0.73      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['3'])).
% 0.51/0.73  thf(d1_xboole_0, axiom,
% 0.51/0.73    (![A:$i]:
% 0.51/0.73     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.73  thf('6', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(l27_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.51/0.73  thf('7', plain,
% 0.51/0.73      (![X49 : $i, X50 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ (k1_tarski @ X49) @ X50) | (r2_hidden @ X49 @ X50))),
% 0.51/0.73      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)
% 0.51/0.73          | (r2_hidden @ sk_A @ X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['6', '7'])).
% 0.51/0.73  thf(t7_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('9', plain,
% 0.51/0.73      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 0.51/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.73  thf(t28_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.51/0.73  thf('10', plain,
% 0.51/0.73      (![X27 : $i, X28 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 0.51/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.73  thf('12', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf(t4_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.73            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.73       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.73            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.51/0.73          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.51/0.73      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.51/0.73          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.73  thf('15', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X2 @ X0)
% 0.51/0.73          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['11', '14'])).
% 0.51/0.73  thf('16', plain,
% 0.51/0.73      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['8', '15'])).
% 0.51/0.73  thf('17', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['5', '16'])).
% 0.51/0.73  thf(l31_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r2_hidden @ A @ B ) =>
% 0.51/0.73       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.51/0.73  thf('18', plain,
% 0.51/0.73      (![X51 : $i, X52 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X52 @ (k1_tarski @ X51)) = (k1_tarski @ X51))
% 0.51/0.73          | ~ (r2_hidden @ X51 @ X52))),
% 0.51/0.73      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.51/0.73  thf('19', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1)
% 0.51/0.73        | ((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['17', '18'])).
% 0.51/0.73  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.73  thf('22', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('23', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.51/0.73  thf('24', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.51/0.73         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('split', [status(esa)], ['1'])).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.51/0.73         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 0.51/0.73         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['23', '26'])).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['27'])).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 0.51/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.73  thf(l32_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.73  thf('31', plain,
% 0.51/0.73      (![X14 : $i, X16 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 0.51/0.73          | ~ (r1_tarski @ X14 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.73  thf('32', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.73  thf(t36_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 0.51/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.73  thf(t12_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      (![X22 : $i, X23 : $i]:
% 0.51/0.73         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.73  thf('36', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['32', '35'])).
% 0.51/0.73  thf('37', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['29', '36'])).
% 0.51/0.73  thf('38', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('39', plain,
% 0.51/0.73      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('40', plain,
% 0.51/0.73      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.51/0.73         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('split', [status(esa)], ['39'])).
% 0.51/0.73  thf('41', plain,
% 0.51/0.73      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.51/0.73         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['38', '40'])).
% 0.51/0.73  thf('42', plain,
% 0.51/0.73      (((((sk_C_1) != (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1)))
% 0.51/0.73         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['37', '41'])).
% 0.51/0.73  thf('43', plain,
% 0.51/0.73      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.73  thf('44', plain,
% 0.51/0.73      ((((sk_B_1) = (k1_tarski @ sk_A))) | (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['28', '43'])).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['27'])).
% 0.51/0.73  thf('46', plain,
% 0.51/0.73      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.51/0.73  thf('47', plain,
% 0.51/0.73      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.51/0.73      inference('split', [status(esa)], ['39'])).
% 0.51/0.73  thf('48', plain,
% 0.51/0.73      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.51/0.73         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('49', plain,
% 0.51/0.73      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['48'])).
% 0.51/0.73  thf('50', plain,
% 0.51/0.73      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['45', '49'])).
% 0.51/0.73  thf('51', plain,
% 0.51/0.73      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.51/0.73      inference('split', [status(esa)], ['39'])).
% 0.51/0.73  thf('52', plain,
% 0.51/0.73      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('split', [status(esa)], ['1'])).
% 0.51/0.73  thf('53', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.51/0.73      inference('sat_resolution*', [status(thm)], ['44', '50', '51', '52'])).
% 0.51/0.73  thf('54', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['4', '53'])).
% 0.51/0.73  thf('55', plain,
% 0.51/0.73      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.51/0.73      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.51/0.73  thf('56', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.51/0.73  thf(t2_boole, axiom,
% 0.51/0.73    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.51/0.73  thf('57', plain,
% 0.51/0.73      (![X29 : $i]: ((k3_xboole_0 @ X29 @ k1_xboole_0) = (k1_xboole_0))),
% 0.51/0.73      inference('cnf', [status(esa)], [t2_boole])).
% 0.51/0.73  thf(t100_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.51/0.73  thf('58', plain,
% 0.51/0.73      (![X17 : $i, X18 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X17 @ X18)
% 0.51/0.73           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.51/0.73  thf('59', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['57', '58'])).
% 0.51/0.73  thf(t5_boole, axiom,
% 0.51/0.73    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.51/0.73  thf('60', plain, (![X32 : $i]: ((k5_xboole_0 @ X32 @ k1_xboole_0) = (X32))),
% 0.51/0.73      inference('cnf', [status(esa)], [t5_boole])).
% 0.51/0.73  thf('61', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.73      inference('demod', [status(thm)], ['59', '60'])).
% 0.51/0.73  thf('62', plain,
% 0.51/0.73      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 0.51/0.73      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.51/0.73  thf('63', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.51/0.73      inference('sup+', [status(thm)], ['61', '62'])).
% 0.51/0.73  thf(t10_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.51/0.73  thf('64', plain,
% 0.51/0.73      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.51/0.73         (~ (r1_tarski @ X19 @ X20)
% 0.51/0.73          | (r1_tarski @ X19 @ (k2_xboole_0 @ X21 @ X20)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.51/0.73  thf('65', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['63', '64'])).
% 0.51/0.73  thf('66', plain,
% 0.51/0.73      (![X14 : $i, X16 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 0.51/0.73          | ~ (r1_tarski @ X14 @ X16))),
% 0.51/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.73  thf('67', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['65', '66'])).
% 0.51/0.73  thf('68', plain,
% 0.51/0.73      ((((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))
% 0.51/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['56', '67'])).
% 0.51/0.73  thf('69', plain,
% 0.51/0.73      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('simplify', [status(thm)], ['42'])).
% 0.51/0.73  thf('70', plain,
% 0.51/0.73      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('71', plain,
% 0.51/0.73      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.51/0.73       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('split', [status(esa)], ['70'])).
% 0.51/0.73  thf('72', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sat_resolution*', [status(thm)], ['44', '50', '51', '71'])).
% 0.51/0.73  thf('73', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['69', '72'])).
% 0.51/0.73  thf('74', plain, (((k4_xboole_0 @ sk_C_1 @ sk_B_1) = (k1_xboole_0))),
% 0.51/0.73      inference('clc', [status(thm)], ['68', '73'])).
% 0.51/0.73  thf('75', plain,
% 0.51/0.73      (![X14 : $i, X15 : $i]:
% 0.51/0.73         ((r1_tarski @ X14 @ X15)
% 0.51/0.73          | ((k4_xboole_0 @ X14 @ X15) != (k1_xboole_0)))),
% 0.51/0.73      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.51/0.73  thf('76', plain,
% 0.51/0.73      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_C_1 @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['74', '75'])).
% 0.51/0.73  thf('77', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.51/0.73      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.73  thf('78', plain,
% 0.51/0.73      (![X22 : $i, X23 : $i]:
% 0.51/0.73         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.73  thf('79', plain, (((k2_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['77', '78'])).
% 0.51/0.73  thf('80', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.73         (~ (r2_hidden @ X2 @ X0)
% 0.51/0.73          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['11', '14'])).
% 0.51/0.73  thf('81', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (~ (r1_xboole_0 @ sk_B_1 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['79', '80'])).
% 0.51/0.73  thf('82', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 0.51/0.73      inference('simplify', [status(thm)], ['76'])).
% 0.51/0.73  thf('83', plain,
% 0.51/0.73      (![X27 : $i, X28 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 0.51/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.73  thf('84', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['82', '83'])).
% 0.51/0.73  thf('85', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf('86', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['84', '85'])).
% 0.51/0.73  thf('87', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)
% 0.51/0.73          | (r2_hidden @ sk_A @ X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['6', '7'])).
% 0.51/0.73  thf(t83_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.51/0.73  thf('88', plain,
% 0.51/0.73      (![X35 : $i, X36 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ X35 @ X36) = (X35)) | ~ (r1_xboole_0 @ X35 @ X36))),
% 0.51/0.73      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.51/0.73  thf('89', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r2_hidden @ sk_A @ X0)
% 0.51/0.73          | ((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ X0)
% 0.51/0.73              = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['87', '88'])).
% 0.51/0.73  thf('90', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.51/0.73  thf('91', plain,
% 0.51/0.73      (![X33 : $i, X34 : $i]: (r1_tarski @ X33 @ (k2_xboole_0 @ X33 @ X34))),
% 0.51/0.73      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.51/0.73  thf('92', plain,
% 0.51/0.73      (![X22 : $i, X23 : $i]:
% 0.51/0.73         (((k2_xboole_0 @ X23 @ X22) = (X22)) | ~ (r1_tarski @ X23 @ X22))),
% 0.51/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.51/0.73  thf('93', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.51/0.73           = (k2_xboole_0 @ X1 @ X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['91', '92'])).
% 0.51/0.73  thf('94', plain,
% 0.51/0.73      ((((k2_xboole_0 @ sk_B_1 @ sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))
% 0.51/0.73        | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.73      inference('sup+', [status(thm)], ['90', '93'])).
% 0.51/0.73  thf('95', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.51/0.73      inference('demod', [status(thm)], ['59', '60'])).
% 0.51/0.73  thf('96', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.51/0.73      inference('sup-', [status(thm)], ['33', '34'])).
% 0.51/0.73  thf('97', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['95', '96'])).
% 0.51/0.73  thf('98', plain,
% 0.51/0.73      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['94', '97'])).
% 0.51/0.73  thf('99', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['69', '72'])).
% 0.51/0.73  thf('100', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.51/0.73  thf('101', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.51/0.73  thf('102', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r2_hidden @ sk_A @ X0) | ((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['89', '100', '101'])).
% 0.51/0.73  thf('103', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(t69_enumset1, axiom,
% 0.51/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.73  thf('104', plain,
% 0.51/0.73      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 0.51/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.73  thf(l51_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('105', plain,
% 0.51/0.73      (![X53 : $i, X54 : $i]:
% 0.51/0.73         ((k3_tarski @ (k2_tarski @ X53 @ X54)) = (k2_xboole_0 @ X53 @ X54))),
% 0.51/0.73      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.51/0.73  thf('106', plain,
% 0.51/0.73      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['104', '105'])).
% 0.51/0.73  thf('107', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.51/0.73      inference('sup+', [status(thm)], ['95', '96'])).
% 0.51/0.73  thf('108', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.51/0.73      inference('demod', [status(thm)], ['106', '107'])).
% 0.51/0.73  thf('109', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_1)) = (sk_A))),
% 0.51/0.73      inference('sup+', [status(thm)], ['103', '108'])).
% 0.51/0.73  thf('110', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.51/0.73  thf('111', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['109', '110'])).
% 0.51/0.73  thf('112', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r2_hidden @ (k3_tarski @ sk_B_1) @ X0)
% 0.51/0.73          | ((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['102', '111'])).
% 0.51/0.73  thf('113', plain,
% 0.51/0.73      (![X51 : $i, X52 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X52 @ (k1_tarski @ X51)) = (k1_tarski @ X51))
% 0.51/0.73          | ~ (r2_hidden @ X51 @ X52))),
% 0.51/0.73      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.51/0.73  thf('114', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 0.51/0.73          | ((k3_xboole_0 @ X0 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 0.51/0.73              = (k1_tarski @ (k3_tarski @ sk_B_1))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['112', '113'])).
% 0.51/0.73  thf('115', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('116', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('clc', [status(thm)], ['98', '99'])).
% 0.51/0.73  thf('117', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['115', '116'])).
% 0.51/0.73  thf('118', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['109', '110'])).
% 0.51/0.73  thf('119', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.73  thf('120', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.51/0.73      inference('demod', [status(thm)], ['117', '118'])).
% 0.51/0.73  thf('121', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 0.51/0.73          | ((k3_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['114', '119', '120'])).
% 0.51/0.73  thf('122', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf('123', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 0.51/0.73          | ((k4_xboole_0 @ sk_B_1 @ X0) = (sk_B_1)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['121', '122'])).
% 0.51/0.73  thf('124', plain,
% 0.51/0.73      ((((sk_C_1) = (sk_B_1)) | ((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['86', '123'])).
% 0.51/0.73  thf('125', plain,
% 0.51/0.73      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 0.51/0.73      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.51/0.73  thf('126', plain,
% 0.51/0.73      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.51/0.73         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('split', [status(esa)], ['39'])).
% 0.51/0.73  thf('127', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('128', plain,
% 0.51/0.73      ((((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1)))
% 0.51/0.73         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.51/0.73      inference('demod', [status(thm)], ['126', '127'])).
% 0.51/0.73  thf('129', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.51/0.73      inference('sat_resolution*', [status(thm)], ['44', '50', '51', '71'])).
% 0.51/0.73  thf('130', plain, (((sk_C_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['128', '129'])).
% 0.51/0.73  thf('131', plain, ((((sk_C_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['125', '130'])).
% 0.51/0.73  thf('132', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['69', '72'])).
% 0.51/0.73  thf('133', plain, (((sk_C_1) != (sk_B_1))),
% 0.51/0.73      inference('clc', [status(thm)], ['131', '132'])).
% 0.51/0.73  thf('134', plain, (((k4_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_B_1))),
% 0.51/0.73      inference('simplify_reflect-', [status(thm)], ['124', '133'])).
% 0.51/0.73  thf('135', plain,
% 0.51/0.73      (![X35 : $i, X37 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X35 @ X37) | ((k4_xboole_0 @ X35 @ X37) != (X35)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.51/0.73  thf('136', plain,
% 0.51/0.73      ((((sk_B_1) != (sk_B_1)) | (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.51/0.73      inference('sup-', [status(thm)], ['134', '135'])).
% 0.51/0.73  thf('137', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 0.51/0.73      inference('simplify', [status(thm)], ['136'])).
% 0.51/0.73  thf('138', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1)),
% 0.51/0.73      inference('demod', [status(thm)], ['81', '137'])).
% 0.51/0.73  thf('139', plain, ((v1_xboole_0 @ sk_C_1)),
% 0.51/0.73      inference('sup-', [status(thm)], ['55', '138'])).
% 0.51/0.73  thf('140', plain, ($false), inference('demod', [status(thm)], ['54', '139'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
