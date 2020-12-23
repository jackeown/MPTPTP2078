%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rmXmpdZs1L

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:24 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 855 expanded)
%              Number of leaves         :   34 ( 266 expanded)
%              Depth                    :   24
%              Number of atoms          : 1165 (8543 expanded)
%              Number of equality atoms :  167 (1409 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

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
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X67 ) @ X68 )
      | ( r2_hidden @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k4_xboole_0 @ X36 @ X37 )
        = X36 )
      | ~ ( r1_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('6',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X64: $i,X66: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X64 ) @ X66 )
      | ~ ( r2_hidden @ X64 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('12',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X42: $i] :
      ( ( k5_xboole_0 @ X42 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('17',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('21',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
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

thf('24',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X64: $i,X66: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X64 ) @ X66 )
      | ~ ( r2_hidden @ X64 @ X66 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_xboole_0 @ X31 @ X32 )
        = X31 )
      | ~ ( r1_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ sk_B_1 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('39',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_xboole_0 @ X27 @ X26 )
        = X26 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_B_1 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['37','40'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('42',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ~ ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_xboole_0 @ X27 @ X26 )
        = X26 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','47'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('50',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('52',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X42: $i] :
      ( ( k5_xboole_0 @ X42 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('55',plain,(
    ! [X14: $i] :
      ( ( k3_xboole_0 @ X14 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('59',plain,(
    ! [X33: $i] :
      ( ( k5_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('66',plain,(
    ! [X36: $i,X38: $i] :
      ( ( r1_xboole_0 @ X36 @ X38 )
      | ( ( k4_xboole_0 @ X36 @ X38 )
       != X36 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['50','69'])).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k2_xboole_0 @ X27 @ X26 )
        = X26 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','72'])).

thf('74',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['74'])).

thf('76',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('79',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('82',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('89',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['74'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['78','80','92'])).

thf('94',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['77','93'])).

thf('95',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['48','96'])).

thf('98',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['17','97'])).

thf('99',plain,(
    ! [X42: $i] :
      ( ( k5_xboole_0 @ X42 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('100',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X39 @ X40 ) @ X41 )
      = ( k5_xboole_0 @ X39 @ ( k5_xboole_0 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( sk_C_2
      = ( k5_xboole_0 @ sk_B_1 @ k1_xboole_0 ) )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X33: $i] :
      ( ( k5_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('106',plain,
    ( ( sk_C_2 = sk_B_1 )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = sk_B_1 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['77','93'])).

thf('108',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['48','96'])).

thf('109',plain,(
    sk_C_2 != sk_B_1 ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('112',plain,
    ( sk_C_2
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X42: $i] :
      ( ( k5_xboole_0 @ X42 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('114',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('116',plain,
    ( ( sk_B_1
     != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('117',plain,
    ( ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('118',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('119',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('120',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
        = sk_C_2 )
      | ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
        = k1_xboole_0 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['117','122'])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ( k5_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('125',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('126',plain,
    ( ( ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
        = sk_C_2 )
      | ( sk_C_2 = sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['77','93'])).

thf('128',plain,
    ( ( sk_C_2 = sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('130',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['116','128','129'])).

thf('131',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['83'])).

thf('133',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['131','132'])).

thf('134',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['115','133'])).

thf('135',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['114','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rmXmpdZs1L
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.52/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.71  % Solved by: fo/fo7.sh
% 0.52/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.71  % done 504 iterations in 0.261s
% 0.52/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.71  % SZS output start Refutation
% 0.52/0.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.52/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.52/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.52/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.71  thf(sk_B_type, type, sk_B: $i > $i).
% 0.52/0.71  thf(t43_zfmisc_1, conjecture,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.52/0.71          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.71          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.71          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.52/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.71    (~( ![A:$i,B:$i,C:$i]:
% 0.52/0.71        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.52/0.71             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.71             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.52/0.71             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.52/0.71    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.52/0.71  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf(l27_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.52/0.71  thf('1', plain,
% 0.52/0.71      (![X67 : $i, X68 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ (k1_tarski @ X67) @ X68) | (r2_hidden @ X67 @ X68))),
% 0.52/0.71      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.52/0.71  thf('2', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ X0)
% 0.52/0.71          | (r2_hidden @ sk_A @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['0', '1'])).
% 0.52/0.71  thf(t83_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.71  thf('3', plain,
% 0.52/0.71      (![X36 : $i, X37 : $i]:
% 0.52/0.71         (((k4_xboole_0 @ X36 @ X37) = (X36)) | ~ (r1_xboole_0 @ X36 @ X37))),
% 0.52/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.52/0.71  thf('4', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r2_hidden @ sk_A @ X0)
% 0.52/0.71          | ((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ X0)
% 0.52/0.71              = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.71  thf(l98_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k5_xboole_0 @ A @ B ) =
% 0.52/0.71       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('5', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ X20 @ X21)
% 0.52/0.71           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 0.52/0.71              (k3_xboole_0 @ X20 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.52/0.71  thf('6', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.52/0.71        | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['4', '5'])).
% 0.52/0.71  thf(l1_zfmisc_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.52/0.71  thf('7', plain,
% 0.52/0.71      (![X64 : $i, X66 : $i]:
% 0.52/0.71         ((r1_tarski @ (k1_tarski @ X64) @ X66) | ~ (r2_hidden @ X64 @ X66))),
% 0.52/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.52/0.71  thf('8', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.52/0.71        | (r1_tarski @ (k1_tarski @ sk_A) @ (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.71  thf('9', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('10', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.52/0.71        | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ 
% 0.52/0.71           (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['8', '9'])).
% 0.52/0.71  thf(t28_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.52/0.71  thf('11', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('12', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.52/0.71        | ((k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ 
% 0.52/0.71            (k3_xboole_0 @ sk_B_1 @ sk_C_2)) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.71  thf(t100_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.52/0.71  thf('13', plain,
% 0.52/0.71      (![X22 : $i, X23 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X22 @ X23)
% 0.52/0.71           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf('14', plain,
% 0.52/0.71      ((((k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ 
% 0.52/0.71          (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.52/0.71          = (k5_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ 
% 0.52/0.71             (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.52/0.71        | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['12', '13'])).
% 0.52/0.71  thf('15', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ X20 @ X21)
% 0.52/0.71           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 0.52/0.71              (k3_xboole_0 @ X20 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.52/0.71  thf(t92_xboole_1, axiom,
% 0.52/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.52/0.71  thf('16', plain, (![X42 : $i]: ((k5_xboole_0 @ X42 @ X42) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('17', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.52/0.71        | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.52/0.71  thf(d1_xboole_0, axiom,
% 0.52/0.71    (![A:$i]:
% 0.52/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.52/0.71  thf('18', plain,
% 0.52/0.71      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.52/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.52/0.71  thf('19', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ X0)
% 0.52/0.71          | (r2_hidden @ sk_A @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['0', '1'])).
% 0.52/0.71  thf(t7_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.52/0.71  thf('20', plain,
% 0.52/0.71      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 0.52/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.71  thf('21', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('22', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.71  thf(commutativity_k3_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.52/0.71  thf('23', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.71  thf(t4_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.52/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.52/0.71  thf('24', plain,
% 0.52/0.71      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.52/0.71          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.52/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.52/0.71  thf('25', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.71  thf('26', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X2 @ X0)
% 0.52/0.71          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['22', '25'])).
% 0.52/0.71  thf('27', plain,
% 0.52/0.71      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['19', '26'])).
% 0.52/0.71  thf('28', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['18', '27'])).
% 0.52/0.71  thf('29', plain,
% 0.52/0.71      (![X64 : $i, X66 : $i]:
% 0.52/0.71         ((r1_tarski @ (k1_tarski @ X64) @ X66) | ~ (r2_hidden @ X64 @ X66))),
% 0.52/0.71      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.52/0.71  thf('30', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['28', '29'])).
% 0.52/0.71  thf('31', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('32', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1)
% 0.52/0.71        | (r1_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ sk_B_1))),
% 0.52/0.71      inference('demod', [status(thm)], ['30', '31'])).
% 0.52/0.71  thf('33', plain,
% 0.52/0.71      (![X31 : $i, X32 : $i]:
% 0.52/0.71         (((k3_xboole_0 @ X31 @ X32) = (X31)) | ~ (r1_tarski @ X31 @ X32))),
% 0.52/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.52/0.71  thf('34', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1)
% 0.52/0.71        | ((k3_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ sk_B_1)
% 0.52/0.71            = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.71  thf('35', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.52/0.71  thf('36', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['20', '21'])).
% 0.52/0.71  thf('37', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.52/0.71  thf('38', plain,
% 0.52/0.71      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 0.52/0.71      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.52/0.71  thf(t12_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.52/0.71  thf('39', plain,
% 0.52/0.71      (![X26 : $i, X27 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X27 @ X26) = (X26)) | ~ (r1_tarski @ X27 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.71  thf('40', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 0.52/0.71           = (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.71  thf('41', plain,
% 0.52/0.71      ((((k2_xboole_0 @ sk_B_1 @ sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.52/0.71        | (v1_xboole_0 @ sk_B_1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['37', '40'])).
% 0.52/0.71  thf(d3_tarski, axiom,
% 0.52/0.71    (![A:$i,B:$i]:
% 0.52/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.52/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.52/0.71  thf('42', plain,
% 0.52/0.71      (![X8 : $i, X10 : $i]:
% 0.52/0.71         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('43', plain,
% 0.52/0.71      (![X8 : $i, X10 : $i]:
% 0.52/0.71         ((r1_tarski @ X8 @ X10) | ~ (r2_hidden @ (sk_C @ X10 @ X8) @ X10))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('44', plain,
% 0.52/0.71      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['42', '43'])).
% 0.52/0.71  thf('45', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.52/0.71      inference('simplify', [status(thm)], ['44'])).
% 0.52/0.71  thf('46', plain,
% 0.52/0.71      (![X26 : $i, X27 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X27 @ X26) = (X26)) | ~ (r1_tarski @ X27 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.71  thf('47', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('48', plain,
% 0.52/0.71      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)) | (v1_xboole_0 @ sk_B_1))),
% 0.52/0.71      inference('demod', [status(thm)], ['41', '47'])).
% 0.52/0.71  thf(l13_xboole_0, axiom,
% 0.52/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.71  thf('49', plain,
% 0.52/0.71      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('50', plain,
% 0.52/0.71      (![X8 : $i, X10 : $i]:
% 0.52/0.71         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 0.52/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.52/0.71  thf('51', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('52', plain,
% 0.52/0.71      (![X20 : $i, X21 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ X20 @ X21)
% 0.52/0.71           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 0.52/0.71              (k3_xboole_0 @ X20 @ X21)))),
% 0.52/0.71      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.52/0.71  thf('53', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ X0 @ X0)
% 0.52/0.71           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['51', '52'])).
% 0.52/0.71  thf('54', plain, (![X42 : $i]: ((k5_xboole_0 @ X42 @ X42) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf(idempotence_k3_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.52/0.71  thf('55', plain, (![X14 : $i]: ((k3_xboole_0 @ X14 @ X14) = (X14))),
% 0.52/0.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.52/0.71  thf('56', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.52/0.71  thf('57', plain,
% 0.52/0.71      (![X22 : $i, X23 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ X22 @ X23)
% 0.52/0.71           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.52/0.71  thf(commutativity_k5_xboole_0, axiom,
% 0.52/0.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.52/0.71  thf('58', plain,
% 0.52/0.71      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.52/0.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.52/0.71  thf(t5_boole, axiom,
% 0.52/0.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.52/0.71  thf('59', plain, (![X33 : $i]: ((k5_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 0.52/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.71  thf('60', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('61', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['57', '60'])).
% 0.52/0.71  thf('62', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.52/0.71          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.71  thf('63', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.52/0.71          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['61', '62'])).
% 0.52/0.71  thf('64', plain,
% 0.52/0.71      (![X0 : $i]:
% 0.52/0.71         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.52/0.71          | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['56', '63'])).
% 0.52/0.71  thf('65', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.71      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.52/0.71  thf('66', plain,
% 0.52/0.71      (![X36 : $i, X38 : $i]:
% 0.52/0.71         ((r1_xboole_0 @ X36 @ X38) | ((k4_xboole_0 @ X36 @ X38) != (X36)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.52/0.71  thf('67', plain,
% 0.52/0.71      (![X0 : $i]: (((k1_xboole_0) != (X0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['65', '66'])).
% 0.52/0.71  thf('68', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.52/0.71      inference('simplify', [status(thm)], ['67'])).
% 0.52/0.71  thf('69', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.52/0.71      inference('demod', [status(thm)], ['64', '68'])).
% 0.52/0.71  thf('70', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.52/0.71      inference('sup-', [status(thm)], ['50', '69'])).
% 0.52/0.71  thf('71', plain,
% 0.52/0.71      (![X26 : $i, X27 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X27 @ X26) = (X26)) | ~ (r1_tarski @ X27 @ X26))),
% 0.52/0.71      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.71  thf('72', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['70', '71'])).
% 0.52/0.71  thf('73', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['49', '72'])).
% 0.52/0.71  thf('74', plain,
% 0.52/0.71      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('75', plain,
% 0.52/0.71      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.52/0.71         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('split', [status(esa)], ['74'])).
% 0.52/0.71  thf('76', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('77', plain,
% 0.52/0.71      ((((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.52/0.71         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('demod', [status(thm)], ['75', '76'])).
% 0.52/0.71  thf('78', plain,
% 0.52/0.71      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.52/0.71      inference('split', [status(esa)], ['74'])).
% 0.52/0.71  thf('79', plain,
% 0.52/0.71      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('80', plain,
% 0.52/0.71      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.52/0.71       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('split', [status(esa)], ['79'])).
% 0.52/0.71  thf('81', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.52/0.71  thf('82', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('83', plain,
% 0.52/0.71      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.52/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.71  thf('84', plain,
% 0.52/0.71      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('split', [status(esa)], ['83'])).
% 0.52/0.71  thf('85', plain,
% 0.52/0.71      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['82', '84'])).
% 0.52/0.71  thf('86', plain,
% 0.52/0.71      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['81', '85'])).
% 0.52/0.71  thf('87', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('simplify', [status(thm)], ['86'])).
% 0.52/0.71  thf('88', plain,
% 0.52/0.71      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('89', plain,
% 0.52/0.71      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['74'])).
% 0.52/0.71  thf('90', plain,
% 0.52/0.71      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['88', '89'])).
% 0.52/0.71  thf('91', plain,
% 0.52/0.71      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.52/0.71      inference('simplify', [status(thm)], ['90'])).
% 0.52/0.71  thf('92', plain,
% 0.52/0.71      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('sup-', [status(thm)], ['87', '91'])).
% 0.52/0.71  thf('93', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['78', '80', '92'])).
% 0.52/0.71  thf('94', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['77', '93'])).
% 0.52/0.71  thf('95', plain, ((((sk_C_2) != (sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.52/0.71      inference('sup-', [status(thm)], ['73', '94'])).
% 0.52/0.71  thf('96', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.52/0.71      inference('simplify', [status(thm)], ['95'])).
% 0.52/0.71  thf('97', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('clc', [status(thm)], ['48', '96'])).
% 0.52/0.71  thf('98', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.52/0.71        | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['17', '97'])).
% 0.52/0.71  thf('99', plain, (![X42 : $i]: ((k5_xboole_0 @ X42 @ X42) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf(t91_xboole_1, axiom,
% 0.52/0.71    (![A:$i,B:$i,C:$i]:
% 0.52/0.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.52/0.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.52/0.71  thf('100', plain,
% 0.52/0.71      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ (k5_xboole_0 @ X39 @ X40) @ X41)
% 0.52/0.71           = (k5_xboole_0 @ X39 @ (k5_xboole_0 @ X40 @ X41)))),
% 0.52/0.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.52/0.71  thf('101', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.52/0.71           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['99', '100'])).
% 0.52/0.71  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('103', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['101', '102'])).
% 0.52/0.71  thf('104', plain,
% 0.52/0.71      ((((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ k1_xboole_0))
% 0.52/0.71        | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1)))),
% 0.52/0.71      inference('sup+', [status(thm)], ['98', '103'])).
% 0.52/0.71  thf('105', plain, (![X33 : $i]: ((k5_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 0.52/0.71      inference('cnf', [status(esa)], [t5_boole])).
% 0.52/0.71  thf('106', plain,
% 0.52/0.71      ((((sk_C_2) = (sk_B_1)) | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1)))),
% 0.52/0.71      inference('demod', [status(thm)], ['104', '105'])).
% 0.52/0.71  thf('107', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['77', '93'])).
% 0.52/0.71  thf('108', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('clc', [status(thm)], ['48', '96'])).
% 0.52/0.71  thf('109', plain, (((sk_C_2) != (sk_B_1))),
% 0.52/0.71      inference('demod', [status(thm)], ['107', '108'])).
% 0.52/0.71  thf('110', plain, (((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['106', '109'])).
% 0.52/0.71  thf('111', plain,
% 0.52/0.71      (![X0 : $i, X1 : $i]:
% 0.52/0.71         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.52/0.71      inference('demod', [status(thm)], ['101', '102'])).
% 0.52/0.71  thf('112', plain, (((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.52/0.71      inference('sup+', [status(thm)], ['110', '111'])).
% 0.52/0.71  thf('113', plain, (![X42 : $i]: ((k5_xboole_0 @ X42 @ X42) = (k1_xboole_0))),
% 0.52/0.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.52/0.71  thf('114', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.52/0.71      inference('demod', [status(thm)], ['112', '113'])).
% 0.52/0.71  thf('115', plain,
% 0.52/0.71      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.52/0.71      inference('split', [status(esa)], ['83'])).
% 0.52/0.71  thf('116', plain,
% 0.52/0.71      ((((sk_B_1) != (k2_xboole_0 @ sk_B_1 @ sk_C_2)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['82', '84'])).
% 0.52/0.71  thf('117', plain,
% 0.52/0.71      ((((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))
% 0.52/0.71        | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.52/0.71      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.52/0.71  thf('118', plain,
% 0.52/0.71      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('simplify', [status(thm)], ['86'])).
% 0.52/0.71  thf('119', plain,
% 0.52/0.71      (![X15 : $i]: (((X15) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X15))),
% 0.52/0.71      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.52/0.71  thf('120', plain,
% 0.52/0.71      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['118', '119'])).
% 0.52/0.71  thf('121', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.52/0.71      inference('sup+', [status(thm)], ['58', '59'])).
% 0.52/0.71  thf('122', plain,
% 0.52/0.71      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['120', '121'])).
% 0.52/0.71  thf('123', plain,
% 0.52/0.71      (((((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))
% 0.52/0.71         | ((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['117', '122'])).
% 0.52/0.71  thf('124', plain,
% 0.52/0.71      ((![X0 : $i]: ((k5_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup+', [status(thm)], ['120', '121'])).
% 0.52/0.71  thf('125', plain,
% 0.52/0.71      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('sup-', [status(thm)], ['118', '119'])).
% 0.52/0.71  thf('126', plain,
% 0.52/0.71      (((((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2)) | ((sk_C_2) = (sk_B_1))))
% 0.52/0.71         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.52/0.71  thf('127', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['77', '93'])).
% 0.52/0.71  thf('128', plain,
% 0.52/0.71      ((((sk_C_2) = (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['126', '127'])).
% 0.52/0.71  thf('129', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.52/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.52/0.71  thf('130', plain,
% 0.52/0.71      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.52/0.71      inference('demod', [status(thm)], ['116', '128', '129'])).
% 0.52/0.71  thf('131', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('simplify', [status(thm)], ['130'])).
% 0.52/0.71  thf('132', plain,
% 0.52/0.71      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.52/0.71      inference('split', [status(esa)], ['83'])).
% 0.52/0.71  thf('133', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.52/0.71      inference('sat_resolution*', [status(thm)], ['131', '132'])).
% 0.52/0.71  thf('134', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.52/0.71      inference('simpl_trail', [status(thm)], ['115', '133'])).
% 0.52/0.71  thf('135', plain, ($false),
% 0.52/0.71      inference('simplify_reflect-', [status(thm)], ['114', '134'])).
% 0.52/0.71  
% 0.52/0.71  % SZS output end Refutation
% 0.52/0.71  
% 0.52/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
