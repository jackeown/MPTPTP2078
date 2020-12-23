%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Pv0iRDBII

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:29 EST 2020

% Result     : Theorem 8.33s
% Output     : Refutation 8.33s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 403 expanded)
%              Number of leaves         :   31 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          : 1064 (5016 expanded)
%              Number of equality atoms :  141 ( 926 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('5',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X69: $i,X70: $i] :
      ( ( X70
        = ( k1_tarski @ X69 ) )
      | ( X70 = k1_xboole_0 )
      | ~ ( r1_tarski @ X70 @ ( k1_tarski @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','6','22'])).

thf('24',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( ( r1_xboole_0 @ X17 @ X17 )
      | ( X17 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('26',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf('29',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('39',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','39'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('42',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ X23 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('46',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_C_2 @ k1_xboole_0 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','44','45'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X25 @ X26 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ ( k2_xboole_0 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('50',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('51',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','52'])).

thf('54',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('55',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('56',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X67 ) @ X68 )
      | ( r2_hidden @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('59',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('60',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('66',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_tarski @ X19 @ ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('71',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X2 @ X1 )
      | ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['64','74'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('77',plain,(
    ! [X74: $i,X76: $i,X77: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X74 @ X76 ) @ X77 )
      | ~ ( r2_hidden @ X76 @ X77 )
      | ~ ( r2_hidden @ X74 @ X77 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_A ) @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('80',plain,(
    ! [X39: $i] :
      ( ( k2_tarski @ X39 @ X39 )
      = ( k1_tarski @ X39 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('81',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['54','83'])).

thf('85',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('88',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('91',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('92',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','93'])).

thf('95',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('97',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('98',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['25'])).

thf('99',plain,
    ( ( r1_xboole_0 @ k1_xboole_0 @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('101',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_B )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['3','23'])).

thf('107',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('110',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['96','110'])).

thf('112',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['95','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['35','112'])).

thf('114',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','113'])).

thf('115',plain,(
    $false ),
    inference(simplify,[status(thm)],['114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Pv0iRDBII
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:49:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.33/8.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.33/8.56  % Solved by: fo/fo7.sh
% 8.33/8.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.33/8.56  % done 7285 iterations in 8.107s
% 8.33/8.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.33/8.56  % SZS output start Refutation
% 8.33/8.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.33/8.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.33/8.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 8.33/8.56  thf(sk_A_type, type, sk_A: $i).
% 8.33/8.56  thf(sk_B_type, type, sk_B: $i).
% 8.33/8.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.33/8.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.33/8.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 8.33/8.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 8.33/8.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 8.33/8.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 8.33/8.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.33/8.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.33/8.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 8.33/8.56  thf(t43_zfmisc_1, conjecture,
% 8.33/8.56    (![A:$i,B:$i,C:$i]:
% 8.33/8.56     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 8.33/8.56          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 8.33/8.56          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 8.33/8.56          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 8.33/8.56  thf(zf_stmt_0, negated_conjecture,
% 8.33/8.56    (~( ![A:$i,B:$i,C:$i]:
% 8.33/8.56        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 8.33/8.56             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 8.33/8.56             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 8.33/8.56             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 8.33/8.56    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 8.33/8.56  thf('0', plain,
% 8.33/8.56      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf('1', plain,
% 8.33/8.56      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 8.33/8.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('split', [status(esa)], ['0'])).
% 8.33/8.56  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf('3', plain,
% 8.33/8.56      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 8.33/8.56         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('demod', [status(thm)], ['1', '2'])).
% 8.33/8.56  thf('4', plain,
% 8.33/8.56      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 8.33/8.56      inference('split', [status(esa)], ['0'])).
% 8.33/8.56  thf('5', plain,
% 8.33/8.56      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf('6', plain,
% 8.33/8.56      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 8.33/8.56      inference('split', [status(esa)], ['5'])).
% 8.33/8.56  thf(t7_xboole_1, axiom,
% 8.33/8.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 8.33/8.56  thf('7', plain,
% 8.33/8.56      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 8.33/8.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.33/8.56  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf(l3_zfmisc_1, axiom,
% 8.33/8.56    (![A:$i,B:$i]:
% 8.33/8.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 8.33/8.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 8.33/8.56  thf('9', plain,
% 8.33/8.56      (![X69 : $i, X70 : $i]:
% 8.33/8.56         (((X70) = (k1_tarski @ X69))
% 8.33/8.56          | ((X70) = (k1_xboole_0))
% 8.33/8.56          | ~ (r1_tarski @ X70 @ (k1_tarski @ X69)))),
% 8.33/8.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 8.33/8.56  thf('10', plain,
% 8.33/8.56      (![X0 : $i]:
% 8.33/8.56         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 8.33/8.56          | ((X0) = (k1_xboole_0))
% 8.33/8.56          | ((X0) = (k1_tarski @ sk_A)))),
% 8.33/8.56      inference('sup-', [status(thm)], ['8', '9'])).
% 8.33/8.56  thf('11', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf('12', plain,
% 8.33/8.56      (![X0 : $i]:
% 8.33/8.56         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 8.33/8.56          | ((X0) = (k1_xboole_0))
% 8.33/8.56          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 8.33/8.56      inference('demod', [status(thm)], ['10', '11'])).
% 8.33/8.56  thf('13', plain,
% 8.33/8.56      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.56      inference('sup-', [status(thm)], ['7', '12'])).
% 8.33/8.56  thf('14', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf('15', plain,
% 8.33/8.56      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 8.33/8.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.56  thf('16', plain,
% 8.33/8.56      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('split', [status(esa)], ['15'])).
% 8.33/8.56  thf('17', plain,
% 8.33/8.56      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 8.33/8.56         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('sup-', [status(thm)], ['14', '16'])).
% 8.33/8.56  thf('18', plain,
% 8.33/8.56      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 8.33/8.56         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('sup-', [status(thm)], ['13', '17'])).
% 8.33/8.56  thf('19', plain,
% 8.33/8.56      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('simplify', [status(thm)], ['18'])).
% 8.33/8.56  thf('20', plain,
% 8.33/8.56      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 8.33/8.56      inference('split', [status(esa)], ['0'])).
% 8.33/8.56  thf('21', plain,
% 8.33/8.56      ((((sk_B) != (sk_B)))
% 8.33/8.56         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.56      inference('sup-', [status(thm)], ['19', '20'])).
% 8.33/8.56  thf('22', plain,
% 8.33/8.56      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 8.33/8.56      inference('simplify', [status(thm)], ['21'])).
% 8.33/8.56  thf('23', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 8.33/8.56      inference('sat_resolution*', [status(thm)], ['4', '6', '22'])).
% 8.33/8.56  thf('24', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.56      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 8.33/8.56  thf(t66_xboole_1, axiom,
% 8.33/8.56    (![A:$i]:
% 8.33/8.56     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 8.33/8.56       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 8.33/8.56  thf('25', plain,
% 8.33/8.56      (![X17 : $i]: ((r1_xboole_0 @ X17 @ X17) | ((X17) != (k1_xboole_0)))),
% 8.33/8.56      inference('cnf', [status(esa)], [t66_xboole_1])).
% 8.33/8.56  thf('26', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 8.33/8.56      inference('simplify', [status(thm)], ['25'])).
% 8.33/8.56  thf(d3_tarski, axiom,
% 8.33/8.56    (![A:$i,B:$i]:
% 8.33/8.56     ( ( r1_tarski @ A @ B ) <=>
% 8.33/8.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.33/8.56  thf('27', plain,
% 8.33/8.56      (![X3 : $i, X5 : $i]:
% 8.33/8.56         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 8.33/8.56      inference('cnf', [status(esa)], [d3_tarski])).
% 8.33/8.56  thf('28', plain,
% 8.33/8.56      (![X3 : $i, X5 : $i]:
% 8.33/8.56         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 8.33/8.56      inference('cnf', [status(esa)], [d3_tarski])).
% 8.33/8.56  thf(t3_xboole_0, axiom,
% 8.33/8.56    (![A:$i,B:$i]:
% 8.33/8.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 8.33/8.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 8.33/8.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 8.33/8.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 8.33/8.56  thf('29', plain,
% 8.33/8.56      (![X11 : $i, X13 : $i, X14 : $i]:
% 8.33/8.56         (~ (r2_hidden @ X13 @ X11)
% 8.33/8.56          | ~ (r2_hidden @ X13 @ X14)
% 8.33/8.56          | ~ (r1_xboole_0 @ X11 @ X14))),
% 8.33/8.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.56  thf('30', plain,
% 8.33/8.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.56         ((r1_tarski @ X0 @ X1)
% 8.33/8.56          | ~ (r1_xboole_0 @ X0 @ X2)
% 8.33/8.56          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 8.33/8.56      inference('sup-', [status(thm)], ['28', '29'])).
% 8.33/8.56  thf('31', plain,
% 8.33/8.56      (![X0 : $i, X1 : $i]:
% 8.33/8.56         ((r1_tarski @ X0 @ X1)
% 8.33/8.56          | ~ (r1_xboole_0 @ X0 @ X0)
% 8.33/8.56          | (r1_tarski @ X0 @ X1))),
% 8.33/8.56      inference('sup-', [status(thm)], ['27', '30'])).
% 8.33/8.56  thf('32', plain,
% 8.33/8.56      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 8.33/8.56      inference('simplify', [status(thm)], ['31'])).
% 8.33/8.56  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 8.33/8.56      inference('sup-', [status(thm)], ['26', '32'])).
% 8.33/8.56  thf(t12_xboole_1, axiom,
% 8.33/8.56    (![A:$i,B:$i]:
% 8.33/8.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 8.33/8.56  thf('34', plain,
% 8.33/8.56      (![X15 : $i, X16 : $i]:
% 8.33/8.56         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 8.33/8.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.33/8.56  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 8.33/8.56      inference('sup-', [status(thm)], ['33', '34'])).
% 8.33/8.56  thf('36', plain,
% 8.33/8.56      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.56      inference('sup-', [status(thm)], ['7', '12'])).
% 8.33/8.56  thf(t95_xboole_1, axiom,
% 8.33/8.56    (![A:$i,B:$i]:
% 8.33/8.56     ( ( k3_xboole_0 @ A @ B ) =
% 8.33/8.56       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 8.33/8.56  thf('37', plain,
% 8.33/8.56      (![X25 : $i, X26 : $i]:
% 8.33/8.56         ((k3_xboole_0 @ X25 @ X26)
% 8.33/8.56           = (k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ 
% 8.33/8.56              (k2_xboole_0 @ X25 @ X26)))),
% 8.33/8.56      inference('cnf', [status(esa)], [t95_xboole_1])).
% 8.33/8.56  thf(t91_xboole_1, axiom,
% 8.33/8.56    (![A:$i,B:$i,C:$i]:
% 8.33/8.56     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 8.33/8.56       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 8.33/8.56  thf('38', plain,
% 8.33/8.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.33/8.56         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 8.33/8.56           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 8.33/8.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 8.33/8.56  thf('39', plain,
% 8.33/8.56      (![X25 : $i, X26 : $i]:
% 8.33/8.56         ((k3_xboole_0 @ X25 @ X26)
% 8.33/8.56           = (k5_xboole_0 @ X25 @ 
% 8.33/8.56              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 8.33/8.56      inference('demod', [status(thm)], ['37', '38'])).
% 8.33/8.56  thf('40', plain,
% 8.33/8.56      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 8.33/8.56          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 8.33/8.56        | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.56      inference('sup+', [status(thm)], ['36', '39'])).
% 8.33/8.56  thf(commutativity_k5_xboole_0, axiom,
% 8.33/8.56    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 8.33/8.56  thf('41', plain,
% 8.33/8.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 8.33/8.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 8.33/8.56  thf(t92_xboole_1, axiom,
% 8.33/8.56    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 8.33/8.56  thf('42', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 8.33/8.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 8.33/8.56  thf('43', plain,
% 8.33/8.56      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.33/8.56         ((k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ X23)
% 8.33/8.56           = (k5_xboole_0 @ X21 @ (k5_xboole_0 @ X22 @ X23)))),
% 8.33/8.56      inference('cnf', [status(esa)], [t91_xboole_1])).
% 8.33/8.56  thf('44', plain,
% 8.33/8.56      (![X0 : $i, X1 : $i]:
% 8.33/8.56         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 8.33/8.56           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 8.33/8.56      inference('sup+', [status(thm)], ['42', '43'])).
% 8.33/8.56  thf('45', plain,
% 8.33/8.56      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 8.33/8.56      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 8.33/8.56  thf('46', plain,
% 8.33/8.56      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (k5_xboole_0 @ sk_C_2 @ k1_xboole_0))
% 8.33/8.56        | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.56      inference('demod', [status(thm)], ['40', '41', '44', '45'])).
% 8.33/8.56  thf(idempotence_k2_xboole_0, axiom,
% 8.33/8.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 8.33/8.56  thf('47', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 8.33/8.56      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 8.33/8.56  thf('48', plain,
% 8.33/8.56      (![X25 : $i, X26 : $i]:
% 8.33/8.56         ((k3_xboole_0 @ X25 @ X26)
% 8.33/8.56           = (k5_xboole_0 @ X25 @ 
% 8.33/8.56              (k5_xboole_0 @ X26 @ (k2_xboole_0 @ X25 @ X26))))),
% 8.33/8.56      inference('demod', [status(thm)], ['37', '38'])).
% 8.33/8.56  thf('49', plain,
% 8.33/8.56      (![X0 : $i]:
% 8.33/8.56         ((k3_xboole_0 @ X0 @ X0)
% 8.33/8.56           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 8.33/8.56      inference('sup+', [status(thm)], ['47', '48'])).
% 8.33/8.56  thf(idempotence_k3_xboole_0, axiom,
% 8.33/8.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 8.33/8.56  thf('50', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 8.33/8.56      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 8.33/8.56  thf('51', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 8.33/8.56      inference('cnf', [status(esa)], [t92_xboole_1])).
% 8.33/8.56  thf('52', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 8.33/8.56      inference('demod', [status(thm)], ['49', '50', '51'])).
% 8.33/8.56  thf('53', plain,
% 8.33/8.56      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.56      inference('demod', [status(thm)], ['46', '52'])).
% 8.33/8.56  thf('54', plain,
% 8.33/8.56      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.57      inference('sup-', [status(thm)], ['7', '12'])).
% 8.33/8.57  thf('55', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.57  thf(l27_zfmisc_1, axiom,
% 8.33/8.57    (![A:$i,B:$i]:
% 8.33/8.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 8.33/8.57  thf('56', plain,
% 8.33/8.57      (![X67 : $i, X68 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ (k1_tarski @ X67) @ X68) | (r2_hidden @ X67 @ X68))),
% 8.33/8.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 8.33/8.57  thf('57', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 8.33/8.57          | (r2_hidden @ sk_A @ X0))),
% 8.33/8.57      inference('sup+', [status(thm)], ['55', '56'])).
% 8.33/8.57  thf('58', plain,
% 8.33/8.57      (![X11 : $i, X12 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X11))),
% 8.33/8.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.57  thf('59', plain,
% 8.33/8.57      (![X11 : $i, X12 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X12))),
% 8.33/8.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.57  thf('60', plain,
% 8.33/8.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 8.33/8.57         (~ (r2_hidden @ X13 @ X11)
% 8.33/8.57          | ~ (r2_hidden @ X13 @ X14)
% 8.33/8.57          | ~ (r1_xboole_0 @ X11 @ X14))),
% 8.33/8.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.57  thf('61', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X1 @ X0)
% 8.33/8.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 8.33/8.57          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 8.33/8.57      inference('sup-', [status(thm)], ['59', '60'])).
% 8.33/8.57  thf('62', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X0 @ X1)
% 8.33/8.57          | ~ (r1_xboole_0 @ X1 @ X0)
% 8.33/8.57          | (r1_xboole_0 @ X0 @ X1))),
% 8.33/8.57      inference('sup-', [status(thm)], ['58', '61'])).
% 8.33/8.57  thf('63', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i]:
% 8.33/8.57         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 8.33/8.57      inference('simplify', [status(thm)], ['62'])).
% 8.33/8.57  thf('64', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r2_hidden @ sk_A @ X0)
% 8.33/8.57          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 8.33/8.57      inference('sup-', [status(thm)], ['57', '63'])).
% 8.33/8.57  thf('65', plain,
% 8.33/8.57      (![X11 : $i, X12 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X12))),
% 8.33/8.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.57  thf('66', plain,
% 8.33/8.57      (![X19 : $i, X20 : $i]: (r1_tarski @ X19 @ (k2_xboole_0 @ X19 @ X20))),
% 8.33/8.57      inference('cnf', [status(esa)], [t7_xboole_1])).
% 8.33/8.57  thf('67', plain,
% 8.33/8.57      (![X2 : $i, X3 : $i, X4 : $i]:
% 8.33/8.57         (~ (r2_hidden @ X2 @ X3)
% 8.33/8.57          | (r2_hidden @ X2 @ X4)
% 8.33/8.57          | ~ (r1_tarski @ X3 @ X4))),
% 8.33/8.57      inference('cnf', [status(esa)], [d3_tarski])).
% 8.33/8.57  thf('68', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.57         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 8.33/8.57      inference('sup-', [status(thm)], ['66', '67'])).
% 8.33/8.57  thf('69', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X1 @ X0)
% 8.33/8.57          | (r2_hidden @ (sk_C_1 @ X0 @ X1) @ (k2_xboole_0 @ X0 @ X2)))),
% 8.33/8.57      inference('sup-', [status(thm)], ['65', '68'])).
% 8.33/8.57  thf('70', plain,
% 8.33/8.57      (![X11 : $i, X12 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X11 @ X12) | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ X11))),
% 8.33/8.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.57  thf('71', plain,
% 8.33/8.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 8.33/8.57         (~ (r2_hidden @ X13 @ X11)
% 8.33/8.57          | ~ (r2_hidden @ X13 @ X14)
% 8.33/8.57          | ~ (r1_xboole_0 @ X11 @ X14))),
% 8.33/8.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 8.33/8.57  thf('72', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X0 @ X1)
% 8.33/8.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 8.33/8.57          | ~ (r2_hidden @ (sk_C_1 @ X1 @ X0) @ X2))),
% 8.33/8.57      inference('sup-', [status(thm)], ['70', '71'])).
% 8.33/8.57  thf('73', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X2 @ X1)
% 8.33/8.57          | ~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 8.33/8.57          | (r1_xboole_0 @ X2 @ X1))),
% 8.33/8.57      inference('sup-', [status(thm)], ['69', '72'])).
% 8.33/8.57  thf('74', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.33/8.57         (~ (r1_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 8.33/8.57          | (r1_xboole_0 @ X2 @ X1))),
% 8.33/8.57      inference('simplify', [status(thm)], ['73'])).
% 8.33/8.57  thf('75', plain,
% 8.33/8.57      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_B))),
% 8.33/8.57      inference('sup-', [status(thm)], ['64', '74'])).
% 8.33/8.57  thf('76', plain,
% 8.33/8.57      (![X0 : $i]: ((r2_hidden @ sk_A @ X0) | (r1_xboole_0 @ X0 @ sk_B))),
% 8.33/8.57      inference('sup-', [status(thm)], ['64', '74'])).
% 8.33/8.57  thf(t38_zfmisc_1, axiom,
% 8.33/8.57    (![A:$i,B:$i,C:$i]:
% 8.33/8.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 8.33/8.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 8.33/8.57  thf('77', plain,
% 8.33/8.57      (![X74 : $i, X76 : $i, X77 : $i]:
% 8.33/8.57         ((r1_tarski @ (k2_tarski @ X74 @ X76) @ X77)
% 8.33/8.57          | ~ (r2_hidden @ X76 @ X77)
% 8.33/8.57          | ~ (r2_hidden @ X74 @ X77))),
% 8.33/8.57      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 8.33/8.57  thf('78', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X0 @ sk_B)
% 8.33/8.57          | ~ (r2_hidden @ X1 @ X0)
% 8.33/8.57          | (r1_tarski @ (k2_tarski @ X1 @ sk_A) @ X0))),
% 8.33/8.57      inference('sup-', [status(thm)], ['76', '77'])).
% 8.33/8.57  thf('79', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X0 @ sk_B)
% 8.33/8.57          | (r1_tarski @ (k2_tarski @ sk_A @ sk_A) @ X0)
% 8.33/8.57          | (r1_xboole_0 @ X0 @ sk_B))),
% 8.33/8.57      inference('sup-', [status(thm)], ['75', '78'])).
% 8.33/8.57  thf(t69_enumset1, axiom,
% 8.33/8.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 8.33/8.57  thf('80', plain,
% 8.33/8.57      (![X39 : $i]: ((k2_tarski @ X39 @ X39) = (k1_tarski @ X39))),
% 8.33/8.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 8.33/8.57  thf('81', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.33/8.57  thf('82', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X0 @ sk_B)
% 8.33/8.57          | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 8.33/8.57          | (r1_xboole_0 @ X0 @ sk_B))),
% 8.33/8.57      inference('demod', [status(thm)], ['79', '80', '81'])).
% 8.33/8.57  thf('83', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2) @ X0)
% 8.33/8.57          | (r1_xboole_0 @ X0 @ sk_B))),
% 8.33/8.57      inference('simplify', [status(thm)], ['82'])).
% 8.33/8.57  thf('84', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r1_tarski @ sk_B @ X0)
% 8.33/8.57          | ((sk_B) = (k1_xboole_0))
% 8.33/8.57          | (r1_xboole_0 @ X0 @ sk_B))),
% 8.33/8.57      inference('sup+', [status(thm)], ['54', '83'])).
% 8.33/8.57  thf('85', plain,
% 8.33/8.57      (![X15 : $i, X16 : $i]:
% 8.33/8.57         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 8.33/8.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.33/8.57  thf('86', plain,
% 8.33/8.57      (![X0 : $i]:
% 8.33/8.57         ((r1_xboole_0 @ X0 @ sk_B)
% 8.33/8.57          | ((sk_B) = (k1_xboole_0))
% 8.33/8.57          | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 8.33/8.57      inference('sup-', [status(thm)], ['84', '85'])).
% 8.33/8.57  thf('87', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.57      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 8.33/8.57  thf('88', plain,
% 8.33/8.57      ((((sk_C_2) != (sk_C_2))
% 8.33/8.57        | ((sk_B) = (k1_xboole_0))
% 8.33/8.57        | (r1_xboole_0 @ sk_C_2 @ sk_B))),
% 8.33/8.57      inference('sup-', [status(thm)], ['86', '87'])).
% 8.33/8.57  thf('89', plain,
% 8.33/8.57      (((r1_xboole_0 @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.57      inference('simplify', [status(thm)], ['88'])).
% 8.33/8.57  thf('90', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i]:
% 8.33/8.57         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 8.33/8.57      inference('simplify', [status(thm)], ['62'])).
% 8.33/8.57  thf('91', plain,
% 8.33/8.57      ((((sk_B) = (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.57      inference('sup-', [status(thm)], ['89', '90'])).
% 8.33/8.57  thf(d7_xboole_0, axiom,
% 8.33/8.57    (![A:$i,B:$i]:
% 8.33/8.57     ( ( r1_xboole_0 @ A @ B ) <=>
% 8.33/8.57       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 8.33/8.57  thf('92', plain,
% 8.33/8.57      (![X6 : $i, X7 : $i]:
% 8.33/8.57         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 8.33/8.57      inference('cnf', [status(esa)], [d7_xboole_0])).
% 8.33/8.57  thf('93', plain,
% 8.33/8.57      ((((sk_B) = (k1_xboole_0))
% 8.33/8.57        | ((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0)))),
% 8.33/8.57      inference('sup-', [status(thm)], ['91', '92'])).
% 8.33/8.57  thf('94', plain,
% 8.33/8.57      ((((sk_C_2) = (k1_xboole_0))
% 8.33/8.57        | ((sk_B) = (k1_xboole_0))
% 8.33/8.57        | ((sk_B) = (k1_xboole_0)))),
% 8.33/8.57      inference('sup+', [status(thm)], ['53', '93'])).
% 8.33/8.57  thf('95', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 8.33/8.57      inference('simplify', [status(thm)], ['94'])).
% 8.33/8.57  thf('96', plain,
% 8.33/8.57      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 8.33/8.57      inference('split', [status(esa)], ['15'])).
% 8.33/8.57  thf('97', plain,
% 8.33/8.57      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('simplify', [status(thm)], ['18'])).
% 8.33/8.57  thf('98', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 8.33/8.57      inference('simplify', [status(thm)], ['25'])).
% 8.33/8.57  thf('99', plain,
% 8.33/8.57      (((r1_xboole_0 @ k1_xboole_0 @ sk_B))
% 8.33/8.57         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('sup+', [status(thm)], ['97', '98'])).
% 8.33/8.57  thf('100', plain,
% 8.33/8.57      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('simplify', [status(thm)], ['18'])).
% 8.33/8.57  thf('101', plain,
% 8.33/8.57      (((r1_xboole_0 @ sk_B @ sk_B)) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('demod', [status(thm)], ['99', '100'])).
% 8.33/8.57  thf('102', plain,
% 8.33/8.57      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X0 @ X0) | (r1_tarski @ X0 @ X1))),
% 8.33/8.57      inference('simplify', [status(thm)], ['31'])).
% 8.33/8.57  thf('103', plain,
% 8.33/8.57      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 8.33/8.57         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('sup-', [status(thm)], ['101', '102'])).
% 8.33/8.57  thf('104', plain,
% 8.33/8.57      (![X15 : $i, X16 : $i]:
% 8.33/8.57         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 8.33/8.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.33/8.57  thf('105', plain,
% 8.33/8.57      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 8.33/8.57         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('sup-', [status(thm)], ['103', '104'])).
% 8.33/8.57  thf('106', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 8.33/8.57      inference('simpl_trail', [status(thm)], ['3', '23'])).
% 8.33/8.57  thf('107', plain,
% 8.33/8.57      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 8.33/8.57      inference('sup-', [status(thm)], ['105', '106'])).
% 8.33/8.57  thf('108', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 8.33/8.57      inference('simplify', [status(thm)], ['107'])).
% 8.33/8.57  thf('109', plain,
% 8.33/8.57      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 8.33/8.57      inference('split', [status(esa)], ['15'])).
% 8.33/8.57  thf('110', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 8.33/8.57      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 8.33/8.57  thf('111', plain, (((sk_C_2) != (k1_xboole_0))),
% 8.33/8.57      inference('simpl_trail', [status(thm)], ['96', '110'])).
% 8.33/8.57  thf('112', plain, (((sk_B) = (k1_xboole_0))),
% 8.33/8.57      inference('simplify_reflect-', [status(thm)], ['95', '111'])).
% 8.33/8.57  thf('113', plain, (![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0))),
% 8.33/8.57      inference('demod', [status(thm)], ['35', '112'])).
% 8.33/8.57  thf('114', plain, (((sk_C_2) != (sk_C_2))),
% 8.33/8.57      inference('demod', [status(thm)], ['24', '113'])).
% 8.33/8.57  thf('115', plain, ($false), inference('simplify', [status(thm)], ['114'])).
% 8.33/8.57  
% 8.33/8.57  % SZS output end Refutation
% 8.33/8.57  
% 8.33/8.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
