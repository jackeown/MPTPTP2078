%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BgminY5n8k

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:23 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  230 (7065 expanded)
%              Number of leaves         :   38 (2141 expanded)
%              Depth                    :   33
%              Number of atoms          : 1446 (65386 expanded)
%              Number of equality atoms :  201 (10620 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
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

thf('5',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('6',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X67 ) @ X68 )
      | ( r2_hidden @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
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

thf('14',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X64: $i,X66: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X64 ) @ X66 )
      | ~ ( r2_hidden @ X64 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('26',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('30',plain,(
    ! [X28: $i] :
      ( ( k3_xboole_0 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','35'])).

thf('37',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('40',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('43',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['37'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['39','41','47'])).

thf('49',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['38','48'])).

thf('50',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['36','49'])).

thf('51',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('52',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['4','52'])).

thf('54',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('56',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ X30 @ ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('58',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('64',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('65',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ k1_xboole_0 )
      = X29 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('69',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('70',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X69 @ X70 ) )
      = ( k2_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('73',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_xboole_0 @ X20 @ X19 )
        = X19 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['71','75'])).

thf('77',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('78',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X28: $i] :
      ( ( k3_xboole_0 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('84',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('85',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('88',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('92',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['86','92'])).

thf('94',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','93'])).

thf('95',plain,
    ( ( sk_C_1
      = ( k1_tarski @ sk_A ) )
    | ~ ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup+',[status(thm)],['67','94'])).

thf('96',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['38','48'])).

thf('97',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['68','76'])).

thf('99',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['97','98'])).

thf('101',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ sk_B_1 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['62','99','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','17'])).

thf('103',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['97','98'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['97','98'])).

thf('107',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['107','110'])).

thf('112',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['38','48'])).

thf('113',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(clc,[status(thm)],['97','98'])).

thf('114',plain,(
    sk_C_1
 != ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['111','114'])).

thf('116',plain,(
    r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['104','115'])).

thf('117',plain,(
    ! [X64: $i,X66: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X64 ) @ X66 )
      | ~ ( r2_hidden @ X64 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('118',plain,(
    r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['101','118'])).

thf('120',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X67 ) @ X68 )
      | ( r2_hidden @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X64: $i,X66: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X64 ) @ X66 )
      | ~ ( r2_hidden @ X64 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['101','118'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('127',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['101','118'])).

thf('128',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('130',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_1 )
    = ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('131',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('132',plain,(
    ! [X35: $i] :
      ( ( k5_xboole_0 @ X35 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('133',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ X34 )
      = ( k5_xboole_0 @ X32 @ ( k5_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['131','136'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['130','137'])).

thf('139',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('140',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('145',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['138','143','144'])).

thf('146',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X24 @ X25 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('147',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['145','148'])).

thf('150',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['138','143','144'])).

thf('151',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_C_1 )
    | ( sk_B_1 = sk_C_1 ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('153',plain,(
    ! [X28: $i] :
      ( ( k3_xboole_0 @ X28 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('156',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k3_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B_1 @ X0 )
      = ( k3_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k5_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B_1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) )
      = ( k4_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ sk_B_1 @ k1_xboole_0 )
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['154','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
        = ( k4_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('166',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k5_xboole_0 @ X15 @ X16 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X15 @ X16 ) @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X35: $i] :
      ( ( k5_xboole_0 @ X35 @ X35 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('169',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('170',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k3_xboole_0 @ X26 @ X27 )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168','171'])).

thf('173',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('174',plain,
    ( ! [X0: $i] :
        ( sk_C_1
       != ( k4_xboole_0 @ X0 @ X0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('176',plain,(
    ! [X0: $i] :
      ( sk_C_1
     != ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( sk_C_1 != sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['164','176'])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('179',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['38','48'])).

thf('180',plain,
    ( ( sk_C_1 != sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    sk_C_1 != sk_B_1 ),
    inference(clc,[status(thm)],['177','180'])).

thf('182',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['151','181'])).

thf('183',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['125','182'])).

thf('184',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('185',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('186',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['183','186'])).

thf('188',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['138','143','144'])).

thf('189',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    $false ),
    inference(demod,[status(thm)],['53','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BgminY5n8k
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:46:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.58/1.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.58/1.78  % Solved by: fo/fo7.sh
% 1.58/1.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.58/1.78  % done 4392 iterations in 1.331s
% 1.58/1.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.58/1.78  % SZS output start Refutation
% 1.58/1.78  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.58/1.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.58/1.78  thf(sk_A_type, type, sk_A: $i).
% 1.58/1.78  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.58/1.78  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.58/1.78  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.58/1.78  thf(sk_B_type, type, sk_B: $i > $i).
% 1.58/1.78  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.58/1.78  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.58/1.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.58/1.78  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.58/1.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.58/1.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.58/1.78  thf(l13_xboole_0, axiom,
% 1.58/1.78    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.58/1.78  thf('0', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf(t43_zfmisc_1, conjecture,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.58/1.78          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.58/1.78          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.58/1.78          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.58/1.78  thf(zf_stmt_0, negated_conjecture,
% 1.58/1.78    (~( ![A:$i,B:$i,C:$i]:
% 1.58/1.78        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.58/1.78             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.58/1.78             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.58/1.78             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.58/1.78    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.58/1.78  thf('1', plain,
% 1.58/1.78      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('2', plain,
% 1.58/1.78      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('split', [status(esa)], ['1'])).
% 1.58/1.78  thf('3', plain,
% 1.58/1.78      ((![X0 : $i]: (((sk_C_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.58/1.78         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['0', '2'])).
% 1.58/1.78  thf('4', plain,
% 1.58/1.78      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('simplify', [status(thm)], ['3'])).
% 1.58/1.78  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(d1_xboole_0, axiom,
% 1.58/1.78    (![A:$i]:
% 1.58/1.78     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.58/1.78  thf('6', plain,
% 1.58/1.78      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.58/1.78  thf(l27_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.58/1.78  thf('7', plain,
% 1.58/1.78      (![X67 : $i, X68 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ (k1_tarski @ X67) @ X68) | (r2_hidden @ X67 @ X68))),
% 1.58/1.78      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.58/1.78  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(t7_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.58/1.78  thf('9', plain,
% 1.58/1.78      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 1.58/1.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.58/1.78  thf('10', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.58/1.78      inference('sup+', [status(thm)], ['8', '9'])).
% 1.58/1.78  thf(t28_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.58/1.78  thf('11', plain,
% 1.58/1.78      (![X26 : $i, X27 : $i]:
% 1.58/1.78         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.58/1.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.58/1.78  thf('12', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['10', '11'])).
% 1.58/1.78  thf(commutativity_k3_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.58/1.78  thf('13', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.58/1.78  thf(t4_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.58/1.78            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.58/1.78       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.58/1.78            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.58/1.78  thf('14', plain,
% 1.58/1.78      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.58/1.78          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.58/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.58/1.78  thf('15', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.58/1.78          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['13', '14'])).
% 1.58/1.78  thf('16', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.58/1.78          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['12', '15'])).
% 1.58/1.78  thf('17', plain,
% 1.58/1.78      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['7', '16'])).
% 1.58/1.78  thf('18', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['6', '17'])).
% 1.58/1.78  thf(l1_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.58/1.78  thf('19', plain,
% 1.58/1.78      (![X64 : $i, X66 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_tarski @ X64) @ X66) | ~ (r2_hidden @ X64 @ X66))),
% 1.58/1.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.58/1.78  thf('20', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['18', '19'])).
% 1.58/1.78  thf('21', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.58/1.78      inference('sup+', [status(thm)], ['8', '9'])).
% 1.58/1.78  thf(d10_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.58/1.78  thf('22', plain,
% 1.58/1.78      (![X12 : $i, X14 : $i]:
% 1.58/1.78         (((X12) = (X14))
% 1.58/1.78          | ~ (r1_tarski @ X14 @ X12)
% 1.58/1.78          | ~ (r1_tarski @ X12 @ X14))),
% 1.58/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.58/1.78  thf('23', plain,
% 1.58/1.78      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.58/1.78        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['21', '22'])).
% 1.58/1.78  thf('24', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['20', '23'])).
% 1.58/1.78  thf('25', plain,
% 1.58/1.78      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.58/1.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('split', [status(esa)], ['1'])).
% 1.58/1.78  thf('26', plain,
% 1.58/1.78      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 1.58/1.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['24', '25'])).
% 1.58/1.78  thf('27', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('simplify', [status(thm)], ['26'])).
% 1.58/1.78  thf('28', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf('29', plain,
% 1.58/1.78      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['27', '28'])).
% 1.58/1.78  thf(t2_boole, axiom,
% 1.58/1.78    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.58/1.78  thf('30', plain,
% 1.58/1.78      (![X28 : $i]: ((k3_xboole_0 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.58/1.78  thf(t17_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.58/1.78  thf('31', plain,
% 1.58/1.78      (![X24 : $i, X25 : $i]: (r1_tarski @ (k3_xboole_0 @ X24 @ X25) @ X24)),
% 1.58/1.78      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.58/1.78  thf('32', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.58/1.78      inference('sup+', [status(thm)], ['30', '31'])).
% 1.58/1.78  thf(t12_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.58/1.78  thf('33', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i]:
% 1.58/1.78         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 1.58/1.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.58/1.78  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.58/1.78  thf('35', plain,
% 1.58/1.78      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 1.58/1.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('sup+', [status(thm)], ['29', '34'])).
% 1.58/1.78  thf('36', plain,
% 1.58/1.78      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 1.58/1.78         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('sup+', [status(thm)], ['5', '35'])).
% 1.58/1.78  thf('37', plain,
% 1.58/1.78      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('38', plain,
% 1.58/1.78      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.58/1.78         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('split', [status(esa)], ['37'])).
% 1.58/1.78  thf('39', plain,
% 1.58/1.78      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.58/1.78      inference('split', [status(esa)], ['37'])).
% 1.58/1.78  thf('40', plain,
% 1.58/1.78      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('41', plain,
% 1.58/1.78      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.58/1.78       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('split', [status(esa)], ['40'])).
% 1.58/1.78  thf('42', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.58/1.78      inference('simplify', [status(thm)], ['26'])).
% 1.58/1.78  thf('43', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf('44', plain,
% 1.58/1.78      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('split', [status(esa)], ['37'])).
% 1.58/1.78  thf('45', plain,
% 1.58/1.78      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.58/1.78         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['43', '44'])).
% 1.58/1.78  thf('46', plain,
% 1.58/1.78      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('simplify', [status(thm)], ['45'])).
% 1.58/1.78  thf('47', plain,
% 1.58/1.78      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['42', '46'])).
% 1.58/1.78  thf('48', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('sat_resolution*', [status(thm)], ['39', '41', '47'])).
% 1.58/1.78  thf('49', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['38', '48'])).
% 1.58/1.78  thf('50', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['36', '49'])).
% 1.58/1.78  thf('51', plain,
% 1.58/1.78      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('split', [status(esa)], ['1'])).
% 1.58/1.78  thf('52', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.58/1.78      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 1.58/1.78  thf('53', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['4', '52'])).
% 1.58/1.78  thf('54', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.58/1.78      inference('sup+', [status(thm)], ['8', '9'])).
% 1.58/1.78  thf('55', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i]:
% 1.58/1.78         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 1.58/1.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.58/1.78  thf('56', plain,
% 1.58/1.78      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.58/1.78      inference('sup-', [status(thm)], ['54', '55'])).
% 1.58/1.78  thf('57', plain,
% 1.58/1.78      (![X30 : $i, X31 : $i]: (r1_tarski @ X30 @ (k2_xboole_0 @ X30 @ X31))),
% 1.58/1.78      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.58/1.78  thf('58', plain,
% 1.58/1.78      (![X12 : $i, X14 : $i]:
% 1.58/1.78         (((X12) = (X14))
% 1.58/1.78          | ~ (r1_tarski @ X14 @ X12)
% 1.58/1.78          | ~ (r1_tarski @ X12 @ X14))),
% 1.58/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.58/1.78  thf('59', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 1.58/1.78          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['57', '58'])).
% 1.58/1.78  thf('60', plain,
% 1.58/1.78      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.58/1.78        | ((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['56', '59'])).
% 1.58/1.78  thf('61', plain,
% 1.58/1.78      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.58/1.78      inference('sup-', [status(thm)], ['54', '55'])).
% 1.58/1.78  thf('62', plain,
% 1.58/1.78      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 1.58/1.78        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.58/1.78      inference('demod', [status(thm)], ['60', '61'])).
% 1.58/1.78  thf('63', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf(commutativity_k5_xboole_0, axiom,
% 1.58/1.78    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.58/1.78  thf('64', plain,
% 1.58/1.78      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.58/1.78      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.58/1.78  thf(t5_boole, axiom,
% 1.58/1.78    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.58/1.78  thf('65', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ k1_xboole_0) = (X29))),
% 1.58/1.78      inference('cnf', [status(esa)], [t5_boole])).
% 1.58/1.78  thf('66', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['64', '65'])).
% 1.58/1.78  thf('67', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k5_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['63', '66'])).
% 1.58/1.78  thf('68', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['20', '23'])).
% 1.58/1.78  thf(t69_enumset1, axiom,
% 1.58/1.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.58/1.78  thf('69', plain,
% 1.58/1.78      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.58/1.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.58/1.78  thf(l51_zfmisc_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.58/1.78  thf('70', plain,
% 1.58/1.78      (![X69 : $i, X70 : $i]:
% 1.58/1.78         ((k3_tarski @ (k2_tarski @ X69 @ X70)) = (k2_xboole_0 @ X69 @ X70))),
% 1.58/1.78      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.58/1.78  thf('71', plain,
% 1.58/1.78      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['69', '70'])).
% 1.58/1.78  thf('72', plain,
% 1.58/1.78      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 1.58/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.58/1.78  thf('73', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.58/1.78      inference('simplify', [status(thm)], ['72'])).
% 1.58/1.78  thf('74', plain,
% 1.58/1.78      (![X19 : $i, X20 : $i]:
% 1.58/1.78         (((k2_xboole_0 @ X20 @ X19) = (X19)) | ~ (r1_tarski @ X20 @ X19))),
% 1.58/1.78      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.58/1.78  thf('75', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['73', '74'])).
% 1.58/1.78  thf('76', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['71', '75'])).
% 1.58/1.78  thf('77', plain,
% 1.58/1.78      ((((k3_tarski @ sk_B_1) = (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('sup+', [status(thm)], ['68', '76'])).
% 1.58/1.78  thf('78', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf('79', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.58/1.78  thf('80', plain,
% 1.58/1.78      (![X28 : $i]: ((k3_xboole_0 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.58/1.78  thf('81', plain,
% 1.58/1.78      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['79', '80'])).
% 1.58/1.78  thf('82', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['78', '81'])).
% 1.58/1.78  thf('83', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf(l98_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( k5_xboole_0 @ A @ B ) =
% 1.58/1.78       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.58/1.78  thf('84', plain,
% 1.58/1.78      (![X15 : $i, X16 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ X15 @ X16)
% 1.58/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.58/1.78              (k3_xboole_0 @ X15 @ X16)))),
% 1.58/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.58/1.78  thf('85', plain,
% 1.58/1.78      (((k5_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.58/1.78         = (k4_xboole_0 @ (k1_tarski @ sk_A) @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['83', '84'])).
% 1.58/1.78  thf('86', plain,
% 1.58/1.78      ((((k5_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.58/1.78          = (k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))
% 1.58/1.78        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('sup+', [status(thm)], ['82', '85'])).
% 1.58/1.78  thf('87', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.58/1.78  thf('88', plain,
% 1.58/1.78      (![X15 : $i, X16 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ X15 @ X16)
% 1.58/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.58/1.78              (k3_xboole_0 @ X15 @ X16)))),
% 1.58/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.58/1.78  thf('89', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.58/1.78           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['87', '88'])).
% 1.58/1.78  thf('90', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['64', '65'])).
% 1.58/1.78  thf('91', plain,
% 1.58/1.78      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['79', '80'])).
% 1.58/1.78  thf('92', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.58/1.78  thf('93', plain,
% 1.58/1.78      ((((k5_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_A))
% 1.58/1.78        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['86', '92'])).
% 1.58/1.78  thf('94', plain,
% 1.58/1.78      ((((k3_tarski @ sk_B_1) = (sk_A))
% 1.58/1.78        | ((k5_xboole_0 @ sk_B_1 @ sk_C_1) = (k1_tarski @ sk_A)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['77', '93'])).
% 1.58/1.78  thf('95', plain,
% 1.58/1.78      ((((sk_C_1) = (k1_tarski @ sk_A))
% 1.58/1.78        | ~ (v1_xboole_0 @ sk_B_1)
% 1.58/1.78        | ((k3_tarski @ sk_B_1) = (sk_A)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['67', '94'])).
% 1.58/1.78  thf('96', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['38', '48'])).
% 1.58/1.78  thf('97', plain,
% 1.58/1.78      ((~ (v1_xboole_0 @ sk_B_1) | ((k3_tarski @ sk_B_1) = (sk_A)))),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['95', '96'])).
% 1.58/1.78  thf('98', plain,
% 1.58/1.78      ((((k3_tarski @ sk_B_1) = (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('sup+', [status(thm)], ['68', '76'])).
% 1.58/1.78  thf('99', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.58/1.78      inference('clc', [status(thm)], ['97', '98'])).
% 1.58/1.78  thf('100', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.58/1.78      inference('clc', [status(thm)], ['97', '98'])).
% 1.58/1.78  thf('101', plain,
% 1.58/1.78      ((~ (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ sk_B_1)
% 1.58/1.78        | ((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1)))),
% 1.58/1.78      inference('demod', [status(thm)], ['62', '99', '100'])).
% 1.58/1.78  thf('102', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['6', '17'])).
% 1.58/1.78  thf('103', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.58/1.78      inference('clc', [status(thm)], ['97', '98'])).
% 1.58/1.78  thf('104', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ (k3_tarski @ sk_B_1) @ sk_B_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['102', '103'])).
% 1.58/1.78  thf('105', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.58/1.78  thf('106', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.58/1.78      inference('clc', [status(thm)], ['97', '98'])).
% 1.58/1.78  thf('107', plain,
% 1.58/1.78      (((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['105', '106'])).
% 1.58/1.78  thf('108', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf('109', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['32', '33'])).
% 1.58/1.78  thf('110', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['108', '109'])).
% 1.58/1.78  thf('111', plain,
% 1.58/1.78      ((((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_C_1))
% 1.58/1.78        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('sup+', [status(thm)], ['107', '110'])).
% 1.58/1.78  thf('112', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['38', '48'])).
% 1.58/1.78  thf('113', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.58/1.78      inference('clc', [status(thm)], ['97', '98'])).
% 1.58/1.78  thf('114', plain, (((sk_C_1) != (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 1.58/1.78      inference('demod', [status(thm)], ['112', '113'])).
% 1.58/1.78  thf('115', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['111', '114'])).
% 1.58/1.78  thf('116', plain, ((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_B_1)),
% 1.58/1.78      inference('clc', [status(thm)], ['104', '115'])).
% 1.58/1.78  thf('117', plain,
% 1.58/1.78      (![X64 : $i, X66 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_tarski @ X64) @ X66) | ~ (r2_hidden @ X64 @ X66))),
% 1.58/1.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.58/1.78  thf('118', plain,
% 1.58/1.78      ((r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ sk_B_1)),
% 1.58/1.78      inference('sup-', [status(thm)], ['116', '117'])).
% 1.58/1.78  thf('119', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['101', '118'])).
% 1.58/1.78  thf('120', plain,
% 1.58/1.78      (![X67 : $i, X68 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ (k1_tarski @ X67) @ X68) | (r2_hidden @ X67 @ X68))),
% 1.58/1.78      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.58/1.78  thf('121', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ sk_B_1 @ X0) | (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['119', '120'])).
% 1.58/1.78  thf('122', plain,
% 1.58/1.78      (![X64 : $i, X66 : $i]:
% 1.58/1.78         ((r1_tarski @ (k1_tarski @ X64) @ X66) | ~ (r2_hidden @ X64 @ X66))),
% 1.58/1.78      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.58/1.78  thf('123', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((r1_xboole_0 @ sk_B_1 @ X0)
% 1.58/1.78          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['121', '122'])).
% 1.58/1.78  thf('124', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['101', '118'])).
% 1.58/1.78  thf('125', plain,
% 1.58/1.78      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['123', '124'])).
% 1.58/1.78  thf('126', plain,
% 1.58/1.78      (((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['105', '106'])).
% 1.58/1.78  thf('127', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['101', '118'])).
% 1.58/1.78  thf('128', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['126', '127'])).
% 1.58/1.78  thf('129', plain,
% 1.58/1.78      (![X15 : $i, X16 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ X15 @ X16)
% 1.58/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.58/1.78              (k3_xboole_0 @ X15 @ X16)))),
% 1.58/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.58/1.78  thf('130', plain,
% 1.58/1.78      (((k5_xboole_0 @ sk_B_1 @ sk_C_1)
% 1.58/1.78         = (k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['128', '129'])).
% 1.58/1.78  thf(t100_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i]:
% 1.58/1.78     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.58/1.78  thf('131', plain,
% 1.58/1.78      (![X17 : $i, X18 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X17 @ X18)
% 1.58/1.78           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.58/1.78  thf(t92_xboole_1, axiom,
% 1.58/1.78    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.58/1.78  thf('132', plain, (![X35 : $i]: ((k5_xboole_0 @ X35 @ X35) = (k1_xboole_0))),
% 1.58/1.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.58/1.78  thf(t91_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.58/1.78       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.58/1.78  thf('133', plain,
% 1.58/1.78      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ X34)
% 1.58/1.78           = (k5_xboole_0 @ X32 @ (k5_xboole_0 @ X33 @ X34)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.58/1.78  thf('134', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.58/1.78           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['132', '133'])).
% 1.58/1.78  thf('135', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['64', '65'])).
% 1.58/1.78  thf('136', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['134', '135'])).
% 1.58/1.78  thf('137', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k3_xboole_0 @ X1 @ X0)
% 1.58/1.78           = (k5_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['131', '136'])).
% 1.58/1.78  thf('138', plain,
% 1.58/1.78      (((k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))
% 1.58/1.78         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['130', '137'])).
% 1.58/1.78  thf('139', plain,
% 1.58/1.78      (![X24 : $i, X25 : $i]: (r1_tarski @ (k3_xboole_0 @ X24 @ X25) @ X24)),
% 1.58/1.78      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.58/1.78  thf('140', plain,
% 1.58/1.78      (![X26 : $i, X27 : $i]:
% 1.58/1.78         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.58/1.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.58/1.78  thf('141', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0)
% 1.58/1.78           = (k3_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['139', '140'])).
% 1.58/1.78  thf('142', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.58/1.78  thf('143', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.58/1.78           = (k3_xboole_0 @ X0 @ X1))),
% 1.58/1.78      inference('demod', [status(thm)], ['141', '142'])).
% 1.58/1.78  thf('144', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.58/1.78      inference('demod', [status(thm)], ['134', '135'])).
% 1.58/1.78  thf('145', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['138', '143', '144'])).
% 1.58/1.78  thf('146', plain,
% 1.58/1.78      (![X24 : $i, X25 : $i]: (r1_tarski @ (k3_xboole_0 @ X24 @ X25) @ X24)),
% 1.58/1.78      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.58/1.78  thf('147', plain,
% 1.58/1.78      (![X12 : $i, X14 : $i]:
% 1.58/1.78         (((X12) = (X14))
% 1.58/1.78          | ~ (r1_tarski @ X14 @ X12)
% 1.58/1.78          | ~ (r1_tarski @ X12 @ X14))),
% 1.58/1.78      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.58/1.78  thf('148', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X0 @ X1))
% 1.58/1.78          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['146', '147'])).
% 1.58/1.78  thf('149', plain,
% 1.58/1.78      ((~ (r1_tarski @ sk_B_1 @ sk_C_1)
% 1.58/1.78        | ((sk_B_1) = (k3_xboole_0 @ sk_B_1 @ sk_C_1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['145', '148'])).
% 1.58/1.78  thf('150', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['138', '143', '144'])).
% 1.58/1.78  thf('151', plain,
% 1.58/1.78      ((~ (r1_tarski @ sk_B_1 @ sk_C_1) | ((sk_B_1) = (sk_C_1)))),
% 1.58/1.78      inference('demod', [status(thm)], ['149', '150'])).
% 1.58/1.78  thf('152', plain,
% 1.58/1.78      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.58/1.78      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.58/1.78  thf('153', plain,
% 1.58/1.78      (![X28 : $i]: ((k3_xboole_0 @ X28 @ k1_xboole_0) = (k1_xboole_0))),
% 1.58/1.78      inference('cnf', [status(esa)], [t2_boole])).
% 1.58/1.78  thf('154', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['152', '153'])).
% 1.58/1.78  thf('155', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['10', '11'])).
% 1.58/1.78  thf(t16_xboole_1, axiom,
% 1.58/1.78    (![A:$i,B:$i,C:$i]:
% 1.58/1.78     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.58/1.78       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.58/1.78  thf('156', plain,
% 1.58/1.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.58/1.78         ((k3_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ X23)
% 1.58/1.78           = (k3_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.58/1.78  thf('157', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k3_xboole_0 @ sk_B_1 @ X0)
% 1.58/1.78           = (k3_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['155', '156'])).
% 1.58/1.78  thf('158', plain,
% 1.58/1.78      (![X17 : $i, X18 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X17 @ X18)
% 1.58/1.78           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.58/1.78  thf('159', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 1.58/1.78           = (k5_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ sk_B_1 @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['157', '158'])).
% 1.58/1.78  thf('160', plain,
% 1.58/1.78      (![X17 : $i, X18 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ X17 @ X18)
% 1.58/1.78           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.58/1.78      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.58/1.78  thf('161', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k4_xboole_0 @ sk_B_1 @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 1.58/1.78           = (k4_xboole_0 @ sk_B_1 @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['159', '160'])).
% 1.58/1.78  thf('162', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((k4_xboole_0 @ sk_B_1 @ k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ X0))
% 1.58/1.78          | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('sup+', [status(thm)], ['154', '161'])).
% 1.58/1.78  thf('163', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 1.58/1.78      inference('demod', [status(thm)], ['89', '90', '91'])).
% 1.58/1.78  thf('164', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         (((sk_B_1) = (k4_xboole_0 @ sk_B_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['162', '163'])).
% 1.58/1.78  thf('165', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['73', '74'])).
% 1.58/1.78  thf('166', plain,
% 1.58/1.78      (![X15 : $i, X16 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ X15 @ X16)
% 1.58/1.78           = (k4_xboole_0 @ (k2_xboole_0 @ X15 @ X16) @ 
% 1.58/1.78              (k3_xboole_0 @ X15 @ X16)))),
% 1.58/1.78      inference('cnf', [status(esa)], [l98_xboole_1])).
% 1.58/1.78  thf('167', plain,
% 1.58/1.78      (![X0 : $i]:
% 1.58/1.78         ((k5_xboole_0 @ X0 @ X0)
% 1.58/1.78           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 1.58/1.78      inference('sup+', [status(thm)], ['165', '166'])).
% 1.58/1.78  thf('168', plain, (![X35 : $i]: ((k5_xboole_0 @ X35 @ X35) = (k1_xboole_0))),
% 1.58/1.78      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.58/1.78  thf('169', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 1.58/1.78      inference('simplify', [status(thm)], ['72'])).
% 1.58/1.78  thf('170', plain,
% 1.58/1.78      (![X26 : $i, X27 : $i]:
% 1.58/1.78         (((k3_xboole_0 @ X26 @ X27) = (X26)) | ~ (r1_tarski @ X26 @ X27))),
% 1.58/1.78      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.58/1.78  thf('171', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['169', '170'])).
% 1.58/1.78  thf('172', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 1.58/1.78      inference('demod', [status(thm)], ['167', '168', '171'])).
% 1.58/1.78  thf('173', plain,
% 1.58/1.78      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('split', [status(esa)], ['1'])).
% 1.58/1.78  thf('174', plain,
% 1.58/1.78      ((![X0 : $i]: ((sk_C_1) != (k4_xboole_0 @ X0 @ X0)))
% 1.58/1.78         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.58/1.78      inference('sup-', [status(thm)], ['172', '173'])).
% 1.58/1.78  thf('175', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.58/1.78      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 1.58/1.78  thf('176', plain, (![X0 : $i]: ((sk_C_1) != (k4_xboole_0 @ X0 @ X0))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['174', '175'])).
% 1.58/1.78  thf('177', plain, ((((sk_C_1) != (sk_B_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['164', '176'])).
% 1.58/1.78  thf('178', plain,
% 1.58/1.78      (((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 1.58/1.78      inference('sup-', [status(thm)], ['20', '23'])).
% 1.58/1.78  thf('179', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.58/1.78      inference('simpl_trail', [status(thm)], ['38', '48'])).
% 1.58/1.78  thf('180', plain, ((((sk_C_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['178', '179'])).
% 1.58/1.78  thf('181', plain, (((sk_C_1) != (sk_B_1))),
% 1.58/1.78      inference('clc', [status(thm)], ['177', '180'])).
% 1.58/1.78  thf('182', plain, (~ (r1_tarski @ sk_B_1 @ sk_C_1)),
% 1.58/1.78      inference('simplify_reflect-', [status(thm)], ['151', '181'])).
% 1.58/1.78  thf('183', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 1.58/1.78      inference('sup-', [status(thm)], ['125', '182'])).
% 1.58/1.78  thf('184', plain,
% 1.58/1.78      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 1.58/1.78      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.58/1.78  thf('185', plain,
% 1.58/1.78      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.58/1.78         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.58/1.78          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.58/1.78      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.58/1.78  thf('186', plain,
% 1.58/1.78      (![X0 : $i, X1 : $i]:
% 1.58/1.78         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.58/1.78      inference('sup-', [status(thm)], ['184', '185'])).
% 1.58/1.78  thf('187', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.58/1.78      inference('sup-', [status(thm)], ['183', '186'])).
% 1.58/1.78  thf('188', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.58/1.78      inference('demod', [status(thm)], ['138', '143', '144'])).
% 1.58/1.78  thf('189', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.58/1.78      inference('demod', [status(thm)], ['187', '188'])).
% 1.58/1.78  thf('190', plain, ($false), inference('demod', [status(thm)], ['53', '189'])).
% 1.58/1.78  
% 1.58/1.78  % SZS output end Refutation
% 1.58/1.78  
% 1.58/1.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
