%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s92IzRkZGb

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:28 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 603 expanded)
%              Number of leaves         :   33 ( 187 expanded)
%              Depth                    :   24
%              Number of atoms          : 1175 (6527 expanded)
%              Number of equality atoms :  186 (1229 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_C_2
     != ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k2_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('10',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( r1_tarski @ X24 @ ( k3_tarski @ ( k2_tarski @ X24 @ X25 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X80: $i,X81: $i] :
      ( ( X81
        = ( k1_tarski @ X80 ) )
      | ( X81 = k1_xboole_0 )
      | ~ ( r1_tarski @ X81 @ ( k1_tarski @ X80 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( sk_B
     != ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['6','8','28'])).

thf('30',plain,(
    sk_C_2
 != ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['5','29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X81: $i,X82: $i] :
      ( ( r1_tarski @ X81 @ ( k1_tarski @ X82 ) )
      | ( X81 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('33',plain,(
    ! [X82: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X82 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      = ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X30 @ X31 ) @ ( k2_xboole_0 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('39',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('41',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k5_xboole_0 @ X31 @ ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['37','41'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ k1_xboole_0 )
      = X20 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('48',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43','46'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('51',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('56',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_xboole_0 @ X19 @ X18 )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('58',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X19 @ X18 ) )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ k1_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('60',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('61',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C_1 @ X12 @ X11 ) @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_B
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('64',plain,
    ( ( sk_B
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('65',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('66',plain,(
    ! [X47: $i] :
      ( ( k2_tarski @ X47 @ X47 )
      = ( k1_tarski @ X47 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('67',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('68',plain,(
    ! [X83: $i,X84: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X83 @ X84 ) )
      = ( k2_xboole_0 @ X83 @ X84 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X9 @ X9 ) )
      = X9 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( k3_tarski @ ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    = sk_A ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('73',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('74',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
      = sk_B )
    | ( sk_B = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
      = sk_B ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','71'])).

thf('78',plain,
    ( ( sk_B
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('79',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('80',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X78 ) @ X79 )
      | ( r2_hidden @ X78 @ X79 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('85',plain,(
    ! [X75: $i,X77: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X75 ) @ X77 )
      | ~ ( r2_hidden @ X75 @ X77 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['76','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ( sk_B = k1_xboole_0 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X19 @ X18 ) )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ X0 )
      | ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C_2
 != ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['5','29'])).

thf('92',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ( r1_xboole_0 @ sk_B @ sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( sk_B
      = ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('95',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_xboole_0 @ X30 @ X31 )
      = ( k5_xboole_0 @ X30 @ ( k5_xboole_0 @ X31 @ ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('96',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('98',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X29: $i] :
      ( ( k5_xboole_0 @ X29 @ X29 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('100',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X26 @ X27 ) @ X28 )
      = ( k5_xboole_0 @ X26 @ ( k5_xboole_0 @ X27 @ X28 ) ) ) ),
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
    inference('sup+',[status(thm)],['44','45'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k3_xboole_0 @ X11 @ X14 ) )
      | ~ ( r1_xboole_0 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['93','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','108'])).

thf('110',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('111',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C_2 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X10: $i] :
      ( ( k3_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('113',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['20'])).

thf('115',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('116',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['31','54'])).

thf('117',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X19 @ X18 ) )
        = X18 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('119',plain,
    ( ! [X0: $i] :
        ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
        = X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_C_2
 != ( k3_tarski @ ( k2_tarski @ sk_B @ sk_C_2 ) ) ),
    inference(simpl_trail,[status(thm)],['5','29'])).

thf('121',plain,
    ( ( sk_C_2 != sk_C_2 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,
    ( sk_B
    = ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['20'])).

thf('124',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['122','123'])).

thf('125',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['114','124'])).

thf('126',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['113','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ sk_B @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['59','126'])).

thf('128',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['30','127'])).

thf('129',plain,(
    $false ),
    inference(simplify,[status(thm)],['128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.s92IzRkZGb
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.83/1.04  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.83/1.04  % Solved by: fo/fo7.sh
% 0.83/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.04  % done 1432 iterations in 0.583s
% 0.83/1.04  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.83/1.04  % SZS output start Refutation
% 0.83/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.83/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.04  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.83/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.83/1.04  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.83/1.04  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.83/1.04  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.83/1.04  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.83/1.04  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.83/1.04  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.83/1.04  thf(t43_zfmisc_1, conjecture,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.83/1.04          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.83/1.04          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.83/1.04          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.83/1.04        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.83/1.04             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.83/1.04             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.83/1.04             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.83/1.04  thf('0', plain,
% 0.83/1.04      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.83/1.04         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('split', [status(esa)], ['0'])).
% 0.83/1.04  thf('2', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(l51_zfmisc_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.83/1.04  thf('3', plain,
% 0.83/1.04      (![X83 : $i, X84 : $i]:
% 0.83/1.04         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.04  thf('4', plain,
% 0.83/1.04      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.04      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('5', plain,
% 0.83/1.04      ((((sk_C_2) != (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2))))
% 0.83/1.04         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['1', '4'])).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('split', [status(esa)], ['0'])).
% 0.83/1.04  thf('7', plain,
% 0.83/1.04      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.83/1.04      inference('split', [status(esa)], ['7'])).
% 0.83/1.04  thf(t7_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.83/1.04  thf('9', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i]: (r1_tarski @ X24 @ (k2_xboole_0 @ X24 @ X25))),
% 0.83/1.04      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.83/1.04  thf('10', plain,
% 0.83/1.04      (![X83 : $i, X84 : $i]:
% 0.83/1.04         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.04  thf('11', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i]:
% 0.83/1.04         (r1_tarski @ X24 @ (k3_tarski @ (k2_tarski @ X24 @ X25)))),
% 0.83/1.04      inference('demod', [status(thm)], ['9', '10'])).
% 0.83/1.04  thf('12', plain,
% 0.83/1.04      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.04      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf(l3_zfmisc_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.83/1.04       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.83/1.04  thf('13', plain,
% 0.83/1.04      (![X80 : $i, X81 : $i]:
% 0.83/1.04         (((X81) = (k1_tarski @ X80))
% 0.83/1.04          | ((X81) = (k1_xboole_0))
% 0.83/1.04          | ~ (r1_tarski @ X81 @ (k1_tarski @ X80)))),
% 0.83/1.04      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.04          | ((X0) = (k1_xboole_0))
% 0.83/1.04          | ((X0) = (k1_tarski @ sk_A)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['12', '13'])).
% 0.83/1.04  thf('15', plain,
% 0.83/1.04      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.04      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.04          | ((X0) = (k1_xboole_0))
% 0.83/1.04          | ((X0) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2))))),
% 0.83/1.04      inference('demod', [status(thm)], ['14', '15'])).
% 0.83/1.04  thf('17', plain,
% 0.83/1.04      ((((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.04        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['11', '16'])).
% 0.83/1.04  thf('18', plain,
% 0.83/1.04      (![X83 : $i, X84 : $i]:
% 0.83/1.04         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.04  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('20', plain,
% 0.83/1.04      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('21', plain,
% 0.83/1.04      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('split', [status(esa)], ['20'])).
% 0.83/1.04  thf('22', plain,
% 0.83/1.04      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 0.83/1.04         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['19', '21'])).
% 0.83/1.04  thf('23', plain,
% 0.83/1.04      ((((sk_B) != (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2))))
% 0.83/1.04         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['18', '22'])).
% 0.83/1.04  thf('24', plain,
% 0.83/1.04      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 0.83/1.04         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['17', '23'])).
% 0.83/1.04  thf('25', plain,
% 0.83/1.04      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('simplify', [status(thm)], ['24'])).
% 0.83/1.04  thf('26', plain,
% 0.83/1.04      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.83/1.04      inference('split', [status(esa)], ['0'])).
% 0.83/1.04  thf('27', plain,
% 0.83/1.04      ((((sk_B) != (sk_B)))
% 0.83/1.04         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['25', '26'])).
% 0.83/1.04  thf('28', plain,
% 0.83/1.04      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['27'])).
% 0.83/1.04  thf('29', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.83/1.04      inference('sat_resolution*', [status(thm)], ['6', '8', '28'])).
% 0.83/1.04  thf('30', plain, (((sk_C_2) != (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.04      inference('simpl_trail', [status(thm)], ['5', '29'])).
% 0.83/1.04  thf(d3_tarski, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) <=>
% 0.83/1.04       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.83/1.04  thf('31', plain,
% 0.83/1.04      (![X3 : $i, X5 : $i]:
% 0.83/1.04         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.83/1.04  thf('32', plain,
% 0.83/1.04      (![X81 : $i, X82 : $i]:
% 0.83/1.04         ((r1_tarski @ X81 @ (k1_tarski @ X82)) | ((X81) != (k1_xboole_0)))),
% 0.83/1.04      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.83/1.04  thf('33', plain,
% 0.83/1.04      (![X82 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X82))),
% 0.83/1.04      inference('simplify', [status(thm)], ['32'])).
% 0.83/1.04  thf(t12_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.83/1.04  thf('34', plain,
% 0.83/1.04      (![X18 : $i, X19 : $i]:
% 0.83/1.04         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.83/1.04  thf('35', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['33', '34'])).
% 0.83/1.04  thf('36', plain,
% 0.83/1.04      (![X83 : $i, X84 : $i]:
% 0.83/1.04         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.04  thf('37', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.83/1.04           = (k1_tarski @ X0))),
% 0.83/1.04      inference('demod', [status(thm)], ['35', '36'])).
% 0.83/1.04  thf(t95_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( k3_xboole_0 @ A @ B ) =
% 0.83/1.04       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.83/1.04  thf('38', plain,
% 0.83/1.04      (![X30 : $i, X31 : $i]:
% 0.83/1.04         ((k3_xboole_0 @ X30 @ X31)
% 0.83/1.04           = (k5_xboole_0 @ (k5_xboole_0 @ X30 @ X31) @ 
% 0.83/1.04              (k2_xboole_0 @ X30 @ X31)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.83/1.04  thf('39', plain,
% 0.83/1.04      (![X83 : $i, X84 : $i]:
% 0.83/1.04         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.04      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.04  thf(t91_xboole_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.83/1.04       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.83/1.04  thf('40', plain,
% 0.83/1.04      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.83/1.04         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.83/1.04           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.04  thf('41', plain,
% 0.83/1.04      (![X30 : $i, X31 : $i]:
% 0.83/1.04         ((k3_xboole_0 @ X30 @ X31)
% 0.83/1.04           = (k5_xboole_0 @ X30 @ 
% 0.83/1.04              (k5_xboole_0 @ X31 @ (k3_tarski @ (k2_tarski @ X30 @ X31)))))),
% 0.83/1.04      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.83/1.04  thf('42', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.83/1.04           = (k5_xboole_0 @ k1_xboole_0 @ 
% 0.83/1.04              (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))))),
% 0.83/1.04      inference('sup+', [status(thm)], ['37', '41'])).
% 0.83/1.04  thf(t92_xboole_1, axiom,
% 0.83/1.04    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.83/1.04  thf('43', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.83/1.04      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.83/1.04  thf(commutativity_k5_xboole_0, axiom,
% 0.83/1.04    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.83/1.04  thf('44', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.04      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.04  thf(t5_boole, axiom,
% 0.83/1.04    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.83/1.04  thf('45', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ k1_xboole_0) = (X20))),
% 0.83/1.04      inference('cnf', [status(esa)], [t5_boole])).
% 0.83/1.04  thf('46', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.83/1.04      inference('sup+', [status(thm)], ['44', '45'])).
% 0.83/1.04  thf('47', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.83/1.04      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.83/1.04  thf(t4_xboole_0, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.83/1.04            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.83/1.04       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.83/1.04            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.83/1.04  thf('48', plain,
% 0.83/1.04      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.83/1.04         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.83/1.04          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.83/1.04      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.04  thf('49', plain,
% 0.83/1.04      (![X0 : $i, X1 : $i]:
% 0.83/1.04         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.83/1.04          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['47', '48'])).
% 0.83/1.04  thf('50', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.83/1.04      inference('demod', [status(thm)], ['42', '43', '46'])).
% 0.83/1.04  thf(d7_xboole_0, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.83/1.04       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.83/1.04  thf('51', plain,
% 0.83/1.04      (![X6 : $i, X8 : $i]:
% 0.83/1.04         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.83/1.04      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.83/1.04  thf('52', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k1_xboole_0) != (k1_xboole_0))
% 0.83/1.04          | (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['50', '51'])).
% 0.83/1.05  thf('53', plain,
% 0.83/1.05      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['52'])).
% 0.83/1.05  thf('54', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.83/1.05      inference('demod', [status(thm)], ['49', '53'])).
% 0.83/1.05  thf('55', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.05      inference('sup-', [status(thm)], ['31', '54'])).
% 0.83/1.05  thf('56', plain,
% 0.83/1.05      (![X18 : $i, X19 : $i]:
% 0.83/1.05         (((k2_xboole_0 @ X19 @ X18) = (X18)) | ~ (r1_tarski @ X19 @ X18))),
% 0.83/1.05      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.83/1.05  thf('57', plain,
% 0.83/1.05      (![X83 : $i, X84 : $i]:
% 0.83/1.05         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.05  thf('58', plain,
% 0.83/1.05      (![X18 : $i, X19 : $i]:
% 0.83/1.05         (((k3_tarski @ (k2_tarski @ X19 @ X18)) = (X18))
% 0.83/1.05          | ~ (r1_tarski @ X19 @ X18))),
% 0.83/1.05      inference('demod', [status(thm)], ['56', '57'])).
% 0.83/1.05  thf('59', plain,
% 0.83/1.05      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ k1_xboole_0 @ X0)) = (X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['55', '58'])).
% 0.83/1.05  thf(idempotence_k3_xboole_0, axiom,
% 0.83/1.05    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.83/1.05  thf('60', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.83/1.05      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.83/1.05  thf('61', plain,
% 0.83/1.05      (![X11 : $i, X12 : $i]:
% 0.83/1.05         ((r1_xboole_0 @ X11 @ X12)
% 0.83/1.05          | (r2_hidden @ (sk_C_1 @ X12 @ X11) @ (k3_xboole_0 @ X11 @ X12)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.05  thf('62', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r2_hidden @ (sk_C_1 @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['60', '61'])).
% 0.83/1.05  thf('63', plain,
% 0.83/1.05      ((((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['11', '16'])).
% 0.83/1.05  thf('64', plain,
% 0.83/1.05      ((((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['11', '16'])).
% 0.83/1.05  thf('65', plain,
% 0.83/1.05      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.05  thf(t69_enumset1, axiom,
% 0.83/1.05    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.83/1.05  thf('66', plain,
% 0.83/1.05      (![X47 : $i]: ((k2_tarski @ X47 @ X47) = (k1_tarski @ X47))),
% 0.83/1.05      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.83/1.05  thf(idempotence_k2_xboole_0, axiom,
% 0.83/1.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.83/1.05  thf('67', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ X9) = (X9))),
% 0.83/1.05      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.83/1.05  thf('68', plain,
% 0.83/1.05      (![X83 : $i, X84 : $i]:
% 0.83/1.05         ((k3_tarski @ (k2_tarski @ X83 @ X84)) = (k2_xboole_0 @ X83 @ X84))),
% 0.83/1.05      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.83/1.05  thf('69', plain, (![X9 : $i]: ((k3_tarski @ (k2_tarski @ X9 @ X9)) = (X9))),
% 0.83/1.05      inference('demod', [status(thm)], ['67', '68'])).
% 0.83/1.05  thf('70', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['66', '69'])).
% 0.83/1.05  thf('71', plain,
% 0.83/1.05      (((k3_tarski @ (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2))) = (sk_A))),
% 0.83/1.05      inference('sup+', [status(thm)], ['65', '70'])).
% 0.83/1.05  thf('72', plain,
% 0.83/1.05      ((((k3_tarski @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['64', '71'])).
% 0.83/1.05  thf('73', plain,
% 0.83/1.05      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.05  thf('74', plain,
% 0.83/1.05      ((((k1_tarski @ (k3_tarski @ sk_B))
% 0.83/1.05          = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['72', '73'])).
% 0.83/1.05  thf('75', plain,
% 0.83/1.05      ((((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['63', '74'])).
% 0.83/1.05  thf('76', plain,
% 0.83/1.05      ((((sk_B) = (k1_xboole_0)) | ((k1_tarski @ (k3_tarski @ sk_B)) = (sk_B)))),
% 0.83/1.05      inference('simplify', [status(thm)], ['75'])).
% 0.83/1.05  thf('77', plain,
% 0.83/1.05      ((((k3_tarski @ sk_B) = (sk_A)) | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['64', '71'])).
% 0.83/1.05  thf('78', plain,
% 0.83/1.05      ((((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['11', '16'])).
% 0.83/1.05  thf('79', plain,
% 0.83/1.05      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.05      inference('demod', [status(thm)], ['2', '3'])).
% 0.83/1.05  thf(l27_zfmisc_1, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.83/1.05  thf('80', plain,
% 0.83/1.05      (![X78 : $i, X79 : $i]:
% 0.83/1.05         ((r1_xboole_0 @ (k1_tarski @ X78) @ X79) | (r2_hidden @ X78 @ X79))),
% 0.83/1.05      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.83/1.05  thf('81', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r1_xboole_0 @ (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)) @ X0)
% 0.83/1.05          | (r2_hidden @ sk_A @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['79', '80'])).
% 0.83/1.05  thf('82', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r1_xboole_0 @ sk_B @ X0)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r2_hidden @ sk_A @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['78', '81'])).
% 0.83/1.05  thf('83', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r2_hidden @ (k3_tarski @ sk_B) @ X0)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r1_xboole_0 @ sk_B @ X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['77', '82'])).
% 0.83/1.05  thf('84', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r1_xboole_0 @ sk_B @ X0)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r2_hidden @ (k3_tarski @ sk_B) @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['83'])).
% 0.83/1.05  thf(l1_zfmisc_1, axiom,
% 0.83/1.05    (![A:$i,B:$i]:
% 0.83/1.05     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.83/1.05  thf('85', plain,
% 0.83/1.05      (![X75 : $i, X77 : $i]:
% 0.83/1.05         ((r1_tarski @ (k1_tarski @ X75) @ X77) | ~ (r2_hidden @ X75 @ X77))),
% 0.83/1.05      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.83/1.05  thf('86', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r1_xboole_0 @ sk_B @ X0)
% 0.83/1.05          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B)) @ X0))),
% 0.83/1.05      inference('sup-', [status(thm)], ['84', '85'])).
% 0.83/1.05  thf('87', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r1_tarski @ sk_B @ X0)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r1_xboole_0 @ sk_B @ X0)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['76', '86'])).
% 0.83/1.05  thf('88', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         ((r1_xboole_0 @ sk_B @ X0)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r1_tarski @ sk_B @ X0))),
% 0.83/1.05      inference('simplify', [status(thm)], ['87'])).
% 0.83/1.05  thf('89', plain,
% 0.83/1.05      (![X18 : $i, X19 : $i]:
% 0.83/1.05         (((k3_tarski @ (k2_tarski @ X19 @ X18)) = (X18))
% 0.83/1.05          | ~ (r1_tarski @ X19 @ X18))),
% 0.83/1.05      inference('demod', [status(thm)], ['56', '57'])).
% 0.83/1.05  thf('90', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((sk_B) = (k1_xboole_0))
% 0.83/1.05          | (r1_xboole_0 @ sk_B @ X0)
% 0.83/1.05          | ((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (X0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['88', '89'])).
% 0.83/1.05  thf('91', plain, (((sk_C_2) != (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.05      inference('simpl_trail', [status(thm)], ['5', '29'])).
% 0.83/1.05  thf('92', plain,
% 0.83/1.05      ((((sk_C_2) != (sk_C_2))
% 0.83/1.05        | (r1_xboole_0 @ sk_B @ sk_C_2)
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['90', '91'])).
% 0.83/1.05  thf('93', plain,
% 0.83/1.05      ((((sk_B) = (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_2))),
% 0.83/1.05      inference('simplify', [status(thm)], ['92'])).
% 0.83/1.05  thf('94', plain,
% 0.83/1.05      ((((sk_B) = (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['11', '16'])).
% 0.83/1.05  thf('95', plain,
% 0.83/1.05      (![X30 : $i, X31 : $i]:
% 0.83/1.05         ((k3_xboole_0 @ X30 @ X31)
% 0.83/1.05           = (k5_xboole_0 @ X30 @ 
% 0.83/1.05              (k5_xboole_0 @ X31 @ (k3_tarski @ (k2_tarski @ X30 @ X31)))))),
% 0.83/1.05      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.83/1.05  thf('96', plain,
% 0.83/1.05      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.83/1.05          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['94', '95'])).
% 0.83/1.05  thf('97', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.83/1.05      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.83/1.05  thf('98', plain,
% 0.83/1.05      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 0.83/1.05          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C_2)))
% 0.83/1.05        | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['96', '97'])).
% 0.83/1.05  thf('99', plain, (![X29 : $i]: ((k5_xboole_0 @ X29 @ X29) = (k1_xboole_0))),
% 0.83/1.05      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.83/1.05  thf('100', plain,
% 0.83/1.05      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ (k5_xboole_0 @ X26 @ X27) @ X28)
% 0.83/1.05           = (k5_xboole_0 @ X26 @ (k5_xboole_0 @ X27 @ X28)))),
% 0.83/1.05      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.83/1.05  thf('101', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.83/1.05           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('sup+', [status(thm)], ['99', '100'])).
% 0.83/1.05  thf('102', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.83/1.05      inference('sup+', [status(thm)], ['44', '45'])).
% 0.83/1.05  thf('103', plain,
% 0.83/1.05      (![X0 : $i, X1 : $i]:
% 0.83/1.05         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['101', '102'])).
% 0.83/1.05  thf('104', plain,
% 0.83/1.05      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['98', '103'])).
% 0.83/1.05  thf('105', plain,
% 0.83/1.05      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.83/1.05         (~ (r2_hidden @ X13 @ (k3_xboole_0 @ X11 @ X14))
% 0.83/1.05          | ~ (r1_xboole_0 @ X11 @ X14))),
% 0.83/1.05      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.83/1.05  thf('106', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (~ (r2_hidden @ X0 @ sk_C_2)
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | ~ (r1_xboole_0 @ sk_B @ sk_C_2))),
% 0.83/1.05      inference('sup-', [status(thm)], ['104', '105'])).
% 0.83/1.05  thf('107', plain,
% 0.83/1.05      (![X0 : $i]:
% 0.83/1.05         (((sk_B) = (k1_xboole_0))
% 0.83/1.05          | ((sk_B) = (k1_xboole_0))
% 0.83/1.05          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.83/1.05      inference('sup-', [status(thm)], ['93', '106'])).
% 0.83/1.05  thf('108', plain,
% 0.83/1.05      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_2) | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('simplify', [status(thm)], ['107'])).
% 0.83/1.05  thf('109', plain,
% 0.83/1.05      (((r1_xboole_0 @ sk_C_2 @ sk_C_2) | ((sk_B) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['62', '108'])).
% 0.83/1.05  thf('110', plain,
% 0.83/1.05      (![X6 : $i, X7 : $i]:
% 0.83/1.05         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.83/1.05      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.83/1.05  thf('111', plain,
% 0.83/1.05      ((((sk_B) = (k1_xboole_0))
% 0.83/1.05        | ((k3_xboole_0 @ sk_C_2 @ sk_C_2) = (k1_xboole_0)))),
% 0.83/1.05      inference('sup-', [status(thm)], ['109', '110'])).
% 0.83/1.05  thf('112', plain, (![X10 : $i]: ((k3_xboole_0 @ X10 @ X10) = (X10))),
% 0.83/1.05      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.83/1.05  thf('113', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.83/1.05      inference('demod', [status(thm)], ['111', '112'])).
% 0.83/1.05  thf('114', plain,
% 0.83/1.05      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.83/1.05      inference('split', [status(esa)], ['20'])).
% 0.83/1.05  thf('115', plain,
% 0.83/1.05      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.05      inference('simplify', [status(thm)], ['24'])).
% 0.83/1.05  thf('116', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.83/1.05      inference('sup-', [status(thm)], ['31', '54'])).
% 0.83/1.05  thf('117', plain,
% 0.83/1.05      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 0.83/1.05         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.05      inference('sup+', [status(thm)], ['115', '116'])).
% 0.83/1.05  thf('118', plain,
% 0.83/1.05      (![X18 : $i, X19 : $i]:
% 0.83/1.05         (((k3_tarski @ (k2_tarski @ X19 @ X18)) = (X18))
% 0.83/1.05          | ~ (r1_tarski @ X19 @ X18))),
% 0.83/1.05      inference('demod', [status(thm)], ['56', '57'])).
% 0.83/1.05  thf('119', plain,
% 0.83/1.05      ((![X0 : $i]: ((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (X0)))
% 0.83/1.05         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.05      inference('sup-', [status(thm)], ['117', '118'])).
% 0.83/1.05  thf('120', plain, (((sk_C_2) != (k3_tarski @ (k2_tarski @ sk_B @ sk_C_2)))),
% 0.83/1.05      inference('simpl_trail', [status(thm)], ['5', '29'])).
% 0.83/1.05  thf('121', plain,
% 0.83/1.05      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 0.83/1.05      inference('sup-', [status(thm)], ['119', '120'])).
% 0.83/1.05  thf('122', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 0.83/1.05      inference('simplify', [status(thm)], ['121'])).
% 0.83/1.05  thf('123', plain,
% 0.83/1.05      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 0.83/1.05      inference('split', [status(esa)], ['20'])).
% 0.83/1.05  thf('124', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.83/1.05      inference('sat_resolution*', [status(thm)], ['122', '123'])).
% 0.83/1.05  thf('125', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.83/1.05      inference('simpl_trail', [status(thm)], ['114', '124'])).
% 0.83/1.05  thf('126', plain, (((sk_B) = (k1_xboole_0))),
% 0.83/1.05      inference('simplify_reflect-', [status(thm)], ['113', '125'])).
% 0.83/1.05  thf('127', plain,
% 0.83/1.05      (![X0 : $i]: ((k3_tarski @ (k2_tarski @ sk_B @ X0)) = (X0))),
% 0.83/1.05      inference('demod', [status(thm)], ['59', '126'])).
% 0.83/1.05  thf('128', plain, (((sk_C_2) != (sk_C_2))),
% 0.83/1.05      inference('demod', [status(thm)], ['30', '127'])).
% 0.83/1.05  thf('129', plain, ($false), inference('simplify', [status(thm)], ['128'])).
% 0.83/1.05  
% 0.83/1.05  % SZS output end Refutation
% 0.83/1.05  
% 0.83/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
