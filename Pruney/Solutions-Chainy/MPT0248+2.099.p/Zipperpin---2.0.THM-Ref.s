%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WDzp4YrIVd

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:32 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 626 expanded)
%              Number of leaves         :   28 ( 178 expanded)
%              Depth                    :   21
%              Number of atoms          :  749 (6923 expanded)
%              Number of equality atoms :  103 (1341 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X55: $i,X56: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X55 ) @ X56 )
      | ( r2_hidden @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('12',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X52 ) @ X54 )
      | ~ ( r2_hidden @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B_1 )
      | ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X11: $i] :
      ( ( X9 = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_xboole_0 @ sk_B_1 @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( X9 != X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['19','21'])).

thf('23',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['23','28'])).

thf('30',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('33',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('36',plain,(
    ! [X57: $i,X58: $i] :
      ( ( X58
        = ( k1_tarski @ X57 ) )
      | ( X58 = k1_xboole_0 )
      | ~ ( r1_tarski @ X58 @ ( k1_tarski @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('37',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('43',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_B_1
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['32','34','44'])).

thf('46',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['31','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','46'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','47'])).

thf('49',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ( r1_xboole_0 @ X18 @ X21 )
      | ~ ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','47'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('56',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('57',plain,(
    ! [X60: $i,X61: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X60 @ X61 ) )
      = ( k2_xboole_0 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('60',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['54','63'])).

thf('65',plain,(
    ! [X52: $i,X54: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X52 ) @ X54 )
      | ~ ( r2_hidden @ X52 @ X54 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','47'])).

thf('68',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['55','62'])).

thf('69',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('73',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X15 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('74',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
      = sk_C_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['38'])).

thf('76',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('77',plain,(
    ! [X14: $i] :
      ( ( r1_xboole_0 @ X14 @ X14 )
      | ( X14 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('78',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('80',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( r1_tarski @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X10: $i] :
      ( r1_tarski @ X10 @ X10 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['76','82'])).

thf('84',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','46'])).

thf('85',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['38'])).

thf('87',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['85','86'])).

thf('88',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['75','87'])).

thf('89',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['74','88'])).

thf('90',plain,(
    sk_B_1 = sk_C_1 ),
    inference('sup+',[status(thm)],['49','89'])).

thf('91',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['31','45'])).

thf('92',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(clc,[status(thm)],['22','47'])).

thf('93',plain,(
    sk_C_1 != sk_B_1 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['90','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WDzp4YrIVd
% 0.14/0.38  % Computer   : n022.cluster.edu
% 0.14/0.38  % Model      : x86_64 x86_64
% 0.14/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.38  % Memory     : 8042.1875MB
% 0.14/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.38  % CPULimit   : 60
% 0.14/0.38  % DateTime   : Tue Dec  1 09:27:26 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.39  % Python version: Python 3.6.8
% 0.14/0.39  % Running in FO mode
% 0.60/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.81  % Solved by: fo/fo7.sh
% 0.60/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.81  % done 921 iterations in 0.318s
% 0.60/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.81  % SZS output start Refutation
% 0.60/0.81  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.81  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.60/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.60/0.81  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.60/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.81  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.81  thf(t43_zfmisc_1, conjecture,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.60/0.81          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.60/0.81          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.60/0.81          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.81    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.81        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.60/0.81             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.60/0.81             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.60/0.81             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.60/0.81    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.60/0.81  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(l27_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.60/0.81  thf('1', plain,
% 0.60/0.81      (![X55 : $i, X56 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ (k1_tarski @ X55) @ X56) | (r2_hidden @ X55 @ X56))),
% 0.60/0.81      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.60/0.81  thf(symmetry_r1_xboole_0, axiom,
% 0.60/0.81    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.60/0.81  thf('2', plain,
% 0.60/0.81      (![X7 : $i, X8 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 0.60/0.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.81  thf('3', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.81  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(t7_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.81  thf('5', plain,
% 0.60/0.81      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.60/0.81      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.60/0.81  thf('6', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.60/0.81      inference('sup+', [status(thm)], ['4', '5'])).
% 0.60/0.81  thf(t12_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.60/0.81  thf('7', plain,
% 0.60/0.81      (![X12 : $i, X13 : $i]:
% 0.60/0.81         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.81  thf('8', plain,
% 0.60/0.81      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.60/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.81  thf(t70_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.60/0.81            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.60/0.81       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.60/0.81            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.60/0.81  thf('9', plain,
% 0.60/0.81      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ X18 @ X19)
% 0.60/0.81          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.60/0.81  thf('10', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.81          | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.81  thf('11', plain,
% 0.60/0.81      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_B_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['3', '10'])).
% 0.60/0.81  thf(l1_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.60/0.81  thf('12', plain,
% 0.60/0.81      (![X52 : $i, X54 : $i]:
% 0.60/0.81         ((r1_tarski @ (k1_tarski @ X52) @ X54) | ~ (r2_hidden @ X52 @ X54))),
% 0.60/0.81      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.60/0.81  thf('13', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ X0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['11', '12'])).
% 0.60/0.81  thf('14', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.60/0.81      inference('sup+', [status(thm)], ['4', '5'])).
% 0.60/0.81  thf(d10_xboole_0, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.81  thf('15', plain,
% 0.60/0.81      (![X9 : $i, X11 : $i]:
% 0.60/0.81         (((X9) = (X11)) | ~ (r1_tarski @ X11 @ X9) | ~ (r1_tarski @ X9 @ X11))),
% 0.60/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.81  thf('16', plain,
% 0.60/0.81      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.60/0.81        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.81  thf('17', plain,
% 0.60/0.81      (((r1_xboole_0 @ sk_B_1 @ sk_B_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['13', '16'])).
% 0.60/0.81  thf(t69_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.60/0.81       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.60/0.81  thf('18', plain,
% 0.60/0.81      (![X16 : $i, X17 : $i]:
% 0.60/0.81         (~ (r1_xboole_0 @ X16 @ X17)
% 0.60/0.81          | ~ (r1_tarski @ X16 @ X17)
% 0.60/0.81          | (v1_xboole_0 @ X16))),
% 0.60/0.81      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.60/0.81  thf('19', plain,
% 0.60/0.81      ((((k1_tarski @ sk_A) = (sk_B_1))
% 0.60/0.81        | (v1_xboole_0 @ sk_B_1)
% 0.60/0.81        | ~ (r1_tarski @ sk_B_1 @ sk_B_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.81  thf('20', plain,
% 0.60/0.81      (![X9 : $i, X10 : $i]: ((r1_tarski @ X9 @ X10) | ((X9) != (X10)))),
% 0.60/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.81  thf('21', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.60/0.81      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.81  thf('22', plain,
% 0.60/0.81      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.60/0.81      inference('demod', [status(thm)], ['19', '21'])).
% 0.60/0.81  thf('23', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(d3_tarski, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( r1_tarski @ A @ B ) <=>
% 0.60/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.60/0.81  thf('24', plain,
% 0.60/0.81      (![X4 : $i, X6 : $i]:
% 0.60/0.81         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.60/0.81      inference('cnf', [status(esa)], [d3_tarski])).
% 0.60/0.81  thf(d1_xboole_0, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.81  thf('25', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.60/0.81      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.60/0.81  thf('26', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.81  thf('27', plain,
% 0.60/0.81      (![X12 : $i, X13 : $i]:
% 0.60/0.81         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.81  thf('28', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (~ (v1_xboole_0 @ X1) | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.81  thf('29', plain,
% 0.60/0.81      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['23', '28'])).
% 0.60/0.81  thf('30', plain,
% 0.60/0.81      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('31', plain,
% 0.60/0.81      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 0.60/0.81         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 0.60/0.81      inference('split', [status(esa)], ['30'])).
% 0.60/0.81  thf('32', plain,
% 0.60/0.81      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.60/0.81      inference('split', [status(esa)], ['30'])).
% 0.60/0.81  thf('33', plain,
% 0.60/0.81      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('34', plain,
% 0.60/0.81      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 0.60/0.81       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.60/0.81      inference('split', [status(esa)], ['33'])).
% 0.60/0.81  thf('35', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.60/0.81      inference('sup+', [status(thm)], ['4', '5'])).
% 0.60/0.81  thf(l3_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.60/0.81       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.60/0.81  thf('36', plain,
% 0.60/0.81      (![X57 : $i, X58 : $i]:
% 0.60/0.81         (((X58) = (k1_tarski @ X57))
% 0.60/0.81          | ((X58) = (k1_xboole_0))
% 0.60/0.81          | ~ (r1_tarski @ X58 @ (k1_tarski @ X57)))),
% 0.60/0.81      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.60/0.81  thf('37', plain,
% 0.60/0.81      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['35', '36'])).
% 0.60/0.81  thf('38', plain,
% 0.60/0.81      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('39', plain,
% 0.60/0.81      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.60/0.81         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.60/0.81      inference('split', [status(esa)], ['38'])).
% 0.60/0.81  thf('40', plain,
% 0.60/0.81      (((((sk_B_1) != (sk_B_1)) | ((sk_B_1) = (k1_xboole_0))))
% 0.60/0.81         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['37', '39'])).
% 0.60/0.81  thf('41', plain,
% 0.60/0.81      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.60/0.81      inference('simplify', [status(thm)], ['40'])).
% 0.60/0.81  thf('42', plain,
% 0.60/0.81      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.60/0.81      inference('split', [status(esa)], ['30'])).
% 0.60/0.81  thf('43', plain,
% 0.60/0.81      ((((sk_B_1) != (sk_B_1)))
% 0.60/0.81         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.60/0.81             ~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.81  thf('44', plain,
% 0.60/0.81      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.60/0.81      inference('simplify', [status(thm)], ['43'])).
% 0.60/0.81  thf('45', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 0.60/0.81      inference('sat_resolution*', [status(thm)], ['32', '34', '44'])).
% 0.60/0.81  thf('46', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.60/0.81      inference('simpl_trail', [status(thm)], ['31', '45'])).
% 0.60/0.81  thf('47', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.60/0.81      inference('simplify_reflect-', [status(thm)], ['29', '46'])).
% 0.60/0.81  thf('48', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.60/0.81      inference('clc', [status(thm)], ['22', '47'])).
% 0.60/0.81  thf('49', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.60/0.81      inference('demod', [status(thm)], ['0', '48'])).
% 0.60/0.81  thf('50', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.81  thf('51', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('52', plain,
% 0.60/0.81      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ X18 @ X21)
% 0.60/0.81          | ~ (r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X21)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.60/0.81  thf('53', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_A))
% 0.60/0.82          | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['51', '52'])).
% 0.60/0.82  thf('54', plain,
% 0.60/0.82      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['50', '53'])).
% 0.60/0.82  thf('55', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.60/0.82      inference('clc', [status(thm)], ['22', '47'])).
% 0.60/0.82  thf(t69_enumset1, axiom,
% 0.60/0.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.82  thf('56', plain,
% 0.60/0.82      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.60/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.82  thf(l51_zfmisc_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.60/0.82  thf('57', plain,
% 0.60/0.82      (![X60 : $i, X61 : $i]:
% 0.60/0.82         ((k3_tarski @ (k2_tarski @ X60 @ X61)) = (k2_xboole_0 @ X60 @ X61))),
% 0.60/0.82      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.60/0.82  thf('58', plain,
% 0.60/0.82      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.60/0.82      inference('sup+', [status(thm)], ['56', '57'])).
% 0.60/0.82  thf('59', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.60/0.82      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.82  thf('60', plain,
% 0.60/0.82      (![X12 : $i, X13 : $i]:
% 0.60/0.82         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.60/0.82      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.82  thf('61', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.82  thf('62', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.60/0.82      inference('demod', [status(thm)], ['58', '61'])).
% 0.60/0.82  thf('63', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.60/0.82      inference('sup+', [status(thm)], ['55', '62'])).
% 0.60/0.82  thf('64', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r2_hidden @ (k3_tarski @ sk_B_1) @ X0) | (r1_xboole_0 @ X0 @ sk_C_1))),
% 0.60/0.82      inference('demod', [status(thm)], ['54', '63'])).
% 0.60/0.82  thf('65', plain,
% 0.60/0.82      (![X52 : $i, X54 : $i]:
% 0.60/0.82         ((r1_tarski @ (k1_tarski @ X52) @ X54) | ~ (r2_hidden @ X52 @ X54))),
% 0.60/0.82      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.60/0.82  thf('66', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r1_xboole_0 @ X0 @ sk_C_1)
% 0.60/0.82          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['64', '65'])).
% 0.60/0.82  thf('67', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.60/0.82      inference('clc', [status(thm)], ['22', '47'])).
% 0.60/0.82  thf('68', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.60/0.82      inference('sup+', [status(thm)], ['55', '62'])).
% 0.60/0.82  thf('69', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.60/0.82      inference('demod', [status(thm)], ['67', '68'])).
% 0.60/0.82  thf('70', plain,
% 0.60/0.82      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_1) | (r1_tarski @ sk_B_1 @ X0))),
% 0.60/0.82      inference('demod', [status(thm)], ['66', '69'])).
% 0.60/0.82  thf('71', plain,
% 0.60/0.82      (![X12 : $i, X13 : $i]:
% 0.60/0.82         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.60/0.82      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.60/0.82  thf('72', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((r1_xboole_0 @ X0 @ sk_C_1) | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['70', '71'])).
% 0.60/0.82  thf(t66_xboole_1, axiom,
% 0.60/0.82    (![A:$i]:
% 0.60/0.82     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.60/0.82       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.60/0.82  thf('73', plain,
% 0.60/0.82      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X15 @ X15))),
% 0.60/0.82      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.60/0.82  thf('74', plain,
% 0.60/0.82      ((((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))
% 0.60/0.82        | ((sk_C_1) = (k1_xboole_0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['72', '73'])).
% 0.60/0.82  thf('75', plain,
% 0.60/0.82      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 0.60/0.82      inference('split', [status(esa)], ['38'])).
% 0.60/0.82  thf('76', plain,
% 0.60/0.82      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.60/0.82      inference('simplify', [status(thm)], ['40'])).
% 0.60/0.82  thf('77', plain,
% 0.60/0.82      (![X14 : $i]: ((r1_xboole_0 @ X14 @ X14) | ((X14) != (k1_xboole_0)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.60/0.82  thf('78', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.60/0.82      inference('simplify', [status(thm)], ['77'])).
% 0.60/0.82  thf('79', plain,
% 0.60/0.82      (![X16 : $i, X17 : $i]:
% 0.60/0.82         (~ (r1_xboole_0 @ X16 @ X17)
% 0.60/0.82          | ~ (r1_tarski @ X16 @ X17)
% 0.60/0.82          | (v1_xboole_0 @ X16))),
% 0.60/0.82      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.60/0.82  thf('80', plain,
% 0.60/0.82      (((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ k1_xboole_0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['78', '79'])).
% 0.60/0.82  thf('81', plain, (![X10 : $i]: (r1_tarski @ X10 @ X10)),
% 0.60/0.82      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.82  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.82      inference('demod', [status(thm)], ['80', '81'])).
% 0.60/0.82  thf('83', plain,
% 0.60/0.82      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.60/0.82      inference('sup+', [status(thm)], ['76', '82'])).
% 0.60/0.82  thf('84', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.60/0.82      inference('simplify_reflect-', [status(thm)], ['29', '46'])).
% 0.60/0.82  thf('85', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['83', '84'])).
% 0.60/0.82  thf('86', plain,
% 0.60/0.82      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.60/0.82      inference('split', [status(esa)], ['38'])).
% 0.60/0.82  thf('87', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 0.60/0.82      inference('sat_resolution*', [status(thm)], ['85', '86'])).
% 0.60/0.82  thf('88', plain, (((sk_C_1) != (k1_xboole_0))),
% 0.60/0.82      inference('simpl_trail', [status(thm)], ['75', '87'])).
% 0.60/0.82  thf('89', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 0.60/0.82      inference('simplify_reflect-', [status(thm)], ['74', '88'])).
% 0.60/0.82  thf('90', plain, (((sk_B_1) = (sk_C_1))),
% 0.60/0.82      inference('sup+', [status(thm)], ['49', '89'])).
% 0.60/0.82  thf('91', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 0.60/0.82      inference('simpl_trail', [status(thm)], ['31', '45'])).
% 0.60/0.82  thf('92', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.60/0.82      inference('clc', [status(thm)], ['22', '47'])).
% 0.60/0.82  thf('93', plain, (((sk_C_1) != (sk_B_1))),
% 0.60/0.82      inference('demod', [status(thm)], ['91', '92'])).
% 0.60/0.82  thf('94', plain, ($false),
% 0.60/0.82      inference('simplify_reflect-', [status(thm)], ['90', '93'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
