%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M6VDadZF6V

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:28 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  190 (4472 expanded)
%              Number of leaves         :   34 (1224 expanded)
%              Depth                    :   34
%              Number of atoms          : 1321 (56103 expanded)
%              Number of equality atoms :  219 (11600 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X67 @ X68 ) )
      = ( k2_xboole_0 @ X67 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('3',plain,(
    ! [X6: $i] :
      ( ( k2_xboole_0 @ X6 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

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
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X64: $i,X65: $i] :
      ( ( X65
        = ( k1_tarski @ X64 ) )
      | ( X65 = k1_xboole_0 )
      | ~ ( r1_tarski @ X65 @ ( k1_tarski @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('15',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_C_2 @ sk_B ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_C_2 ) ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('19',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
      = sk_C_2 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','25'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('28',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_B )
      | ( sk_B = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_C_2
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('39',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('42',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( sk_B
     != ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( sk_B != sk_B )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['34'])).

thf('49',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( sk_B
       != ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['38','40','50'])).

thf('52',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['37','51'])).

thf('53',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['33','52'])).

thf('54',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('55',plain,
    ( ( ( sk_C_2 != sk_C_2 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('57',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('61',plain,(
    ! [X64: $i,X65: $i] :
      ( ( X65
        = ( k1_tarski @ X64 ) )
      | ( X65 = k1_xboole_0 )
      | ~ ( r1_tarski @ X65 @ ( k1_tarski @ X64 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('64',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('72',plain,(
    ! [X59: $i,X60: $i] :
      ( ( r2_hidden @ X59 @ X60 )
      | ~ ( r1_tarski @ ( k1_tarski @ X59 ) @ X60 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('77',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X62 ) @ X63 )
      | ( r2_hidden @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','78'])).

thf('80',plain,(
    ! [X59: $i,X61: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X59 ) @ X61 )
      | ~ ( r2_hidden @ X59 @ X61 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X65: $i,X66: $i] :
      ( ( r1_tarski @ X65 @ ( k1_tarski @ X66 ) )
      | ( X65 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('83',plain,(
    ! [X66: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X66 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('84',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ k1_xboole_0 )
        | ( ( k1_tarski @ X0 )
          = k1_xboole_0 ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['56','86'])).

thf('88',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('89',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ sk_B )
        | ( ( k1_tarski @ X0 )
          = sk_B ) )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('92',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('93',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('94',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','96'])).

thf('98',plain,
    ( ( sk_B
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['43'])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( sk_B != k1_xboole_0 )
        | ( r1_tarski @ k1_xboole_0 @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('101',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( r1_tarski @ sk_B @ X0 ) )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

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
    inference(simpl_trail,[status(thm)],['37','51'])).

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
    inference(split,[status(esa)],['43'])).

thf('110',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ sk_B )
      | ( ( k1_tarski @ X0 )
        = sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['90','110'])).

thf('112',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    | ( r1_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('116',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B @ sk_C_2 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( k3_tarski @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['113','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = sk_A )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ sk_B )
        = sk_A )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['37','51'])).

thf('123',plain,
    ( ( sk_C_2 != sk_C_2 )
    | ( ( k3_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k3_tarski @ sk_B )
    = sk_A ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['5','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','85'])).

thf('127',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('128',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('134',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('135',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('136',plain,(
    sk_B = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['133','134'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = sk_B )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['132','135','136'])).

thf('138',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = sk_B )
      | ( ( k2_xboole_0 @ sk_B @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
        = sk_C_2 )
      | ( ( k1_tarski @ X0 )
        = sk_B ) ) ),
    inference('sup+',[status(thm)],['125','139'])).

thf('141',plain,(
    sk_C_2
 != ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(simpl_trail,[status(thm)],['37','51'])).

thf('142',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B ) )
    = ( k2_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference(demod,[status(thm)],['5','124'])).

thf('143',plain,(
    sk_C_2
 != ( k1_tarski @ ( k3_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
      = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ sk_B )
      = X0 ) ),
    inference(demod,[status(thm)],['4','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ sk_B )
      = X0 ) ),
    inference(demod,[status(thm)],['4','144'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference('sup+',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('149',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('150',plain,
    ( ( sk_C_2 != sk_B )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['108','109'])).

thf('152',plain,(
    sk_C_2 != sk_B ),
    inference(simpl_trail,[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X0: $i] : ( X0 != sk_B ) ),
    inference('sup-',[status(thm)],['147','152'])).

thf('154',plain,(
    $false ),
    inference(simplify,[status(thm)],['153'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M6VDadZF6V
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:45:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.06/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.31  % Solved by: fo/fo7.sh
% 1.06/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.31  % done 1751 iterations in 0.852s
% 1.06/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.31  % SZS output start Refutation
% 1.06/1.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.31  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.06/1.31  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.06/1.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.31  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.31  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.06/1.31  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.06/1.31  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.06/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.31  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.06/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.06/1.31  thf(t69_enumset1, axiom,
% 1.06/1.31    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.06/1.31  thf('0', plain, (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 1.06/1.31      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.06/1.31  thf(l51_zfmisc_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.31  thf('1', plain,
% 1.06/1.31      (![X67 : $i, X68 : $i]:
% 1.06/1.31         ((k3_tarski @ (k2_tarski @ X67 @ X68)) = (k2_xboole_0 @ X67 @ X68))),
% 1.06/1.31      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.06/1.31  thf('2', plain,
% 1.06/1.31      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['0', '1'])).
% 1.06/1.31  thf(idempotence_k2_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.06/1.31  thf('3', plain, (![X6 : $i]: ((k2_xboole_0 @ X6 @ X6) = (X6))),
% 1.06/1.31      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.06/1.31  thf('4', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.06/1.31      inference('demod', [status(thm)], ['2', '3'])).
% 1.06/1.31  thf(t43_zfmisc_1, conjecture,
% 1.06/1.31    (![A:$i,B:$i,C:$i]:
% 1.06/1.31     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.06/1.31          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.06/1.31          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.06/1.31          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.06/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.31    (~( ![A:$i,B:$i,C:$i]:
% 1.06/1.31        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.06/1.31             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.06/1.31             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.06/1.31             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.06/1.31    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.06/1.31  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf(t7_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.06/1.31  thf('6', plain,
% 1.06/1.31      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.06/1.31      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.31  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf(l3_zfmisc_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 1.06/1.31       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 1.06/1.31  thf('8', plain,
% 1.06/1.31      (![X64 : $i, X65 : $i]:
% 1.06/1.31         (((X65) = (k1_tarski @ X64))
% 1.06/1.31          | ((X65) = (k1_xboole_0))
% 1.06/1.31          | ~ (r1_tarski @ X65 @ (k1_tarski @ X64)))),
% 1.06/1.31      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.06/1.31  thf('9', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.06/1.31          | ((X0) = (k1_xboole_0))
% 1.06/1.31          | ((X0) = (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.31  thf('10', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('11', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.06/1.31          | ((X0) = (k1_xboole_0))
% 1.06/1.31          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 1.06/1.31      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.31  thf('12', plain,
% 1.06/1.31      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['6', '11'])).
% 1.06/1.31  thf(t95_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( k3_xboole_0 @ A @ B ) =
% 1.06/1.31       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.06/1.31  thf('13', plain,
% 1.06/1.31      (![X29 : $i, X30 : $i]:
% 1.06/1.31         ((k3_xboole_0 @ X29 @ X30)
% 1.06/1.31           = (k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 1.06/1.31              (k2_xboole_0 @ X29 @ X30)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.06/1.31  thf(t91_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i,C:$i]:
% 1.06/1.31     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.06/1.31       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.06/1.31  thf('14', plain,
% 1.06/1.31      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.06/1.31         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.06/1.31           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.06/1.31  thf('15', plain,
% 1.06/1.31      (![X29 : $i, X30 : $i]:
% 1.06/1.31         ((k3_xboole_0 @ X29 @ X30)
% 1.06/1.31           = (k5_xboole_0 @ X29 @ 
% 1.06/1.31              (k5_xboole_0 @ X30 @ (k2_xboole_0 @ X29 @ X30))))),
% 1.06/1.31      inference('demod', [status(thm)], ['13', '14'])).
% 1.06/1.31  thf('16', plain,
% 1.06/1.31      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 1.06/1.31          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_C_2 @ sk_B)))
% 1.06/1.31        | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['12', '15'])).
% 1.06/1.31  thf(commutativity_k5_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.06/1.31  thf('17', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.31      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.31  thf('18', plain,
% 1.06/1.31      ((((k3_xboole_0 @ sk_B @ sk_C_2)
% 1.06/1.31          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_C_2)))
% 1.06/1.31        | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('demod', [status(thm)], ['16', '17'])).
% 1.06/1.31  thf(t92_xboole_1, axiom,
% 1.06/1.31    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.06/1.31  thf('19', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.06/1.31  thf('20', plain,
% 1.06/1.31      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.06/1.31         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.06/1.31           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.06/1.31  thf('21', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.06/1.31           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['19', '20'])).
% 1.06/1.31  thf('22', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.06/1.31      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.06/1.31  thf(t5_boole, axiom,
% 1.06/1.31    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.06/1.31  thf('23', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 1.06/1.31      inference('cnf', [status(esa)], [t5_boole])).
% 1.06/1.31  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['22', '23'])).
% 1.06/1.31  thf('25', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.31      inference('demod', [status(thm)], ['21', '24'])).
% 1.06/1.31  thf('26', plain,
% 1.06/1.31      ((((k3_xboole_0 @ sk_B @ sk_C_2) = (sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('demod', [status(thm)], ['18', '25'])).
% 1.06/1.31  thf(t17_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.06/1.31  thf('27', plain,
% 1.06/1.31      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 1.06/1.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.06/1.31  thf('28', plain, (((r1_tarski @ sk_C_2 @ sk_B) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['26', '27'])).
% 1.06/1.31  thf('29', plain,
% 1.06/1.31      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['6', '11'])).
% 1.06/1.31  thf('30', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.06/1.31          | ((X0) = (k1_xboole_0))
% 1.06/1.31          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2)))),
% 1.06/1.31      inference('demod', [status(thm)], ['9', '10'])).
% 1.06/1.31  thf('31', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (r1_tarski @ X0 @ sk_B)
% 1.06/1.31          | ((sk_B) = (k1_xboole_0))
% 1.06/1.31          | ((X0) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.06/1.31          | ((X0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['29', '30'])).
% 1.06/1.31  thf('32', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))
% 1.06/1.31        | ((sk_C_2) = (k1_xboole_0))
% 1.06/1.31        | ((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.06/1.31        | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['28', '31'])).
% 1.06/1.31  thf('33', plain,
% 1.06/1.31      ((((sk_C_2) = (k2_xboole_0 @ sk_B @ sk_C_2))
% 1.06/1.31        | ((sk_C_2) = (k1_xboole_0))
% 1.06/1.31        | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('simplify', [status(thm)], ['32'])).
% 1.06/1.31  thf('34', plain,
% 1.06/1.31      ((((sk_B) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('35', plain,
% 1.06/1.31      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 1.06/1.31         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('split', [status(esa)], ['34'])).
% 1.06/1.31  thf('36', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('37', plain,
% 1.06/1.31      ((((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 1.06/1.31         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('demod', [status(thm)], ['35', '36'])).
% 1.06/1.31  thf('38', plain,
% 1.06/1.31      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('split', [status(esa)], ['34'])).
% 1.06/1.31  thf('39', plain,
% 1.06/1.31      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('40', plain,
% 1.06/1.31      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('split', [status(esa)], ['39'])).
% 1.06/1.31  thf('41', plain,
% 1.06/1.31      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['6', '11'])).
% 1.06/1.31  thf('42', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('43', plain,
% 1.06/1.31      ((((sk_B) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('44', plain,
% 1.06/1.31      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('split', [status(esa)], ['43'])).
% 1.06/1.31  thf('45', plain,
% 1.06/1.31      ((((sk_B) != (k2_xboole_0 @ sk_B @ sk_C_2)))
% 1.06/1.31         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['42', '44'])).
% 1.06/1.31  thf('46', plain,
% 1.06/1.31      (((((sk_B) != (sk_B)) | ((sk_B) = (k1_xboole_0))))
% 1.06/1.31         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['41', '45'])).
% 1.06/1.31  thf('47', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['46'])).
% 1.06/1.31  thf('48', plain,
% 1.06/1.31      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 1.06/1.31      inference('split', [status(esa)], ['34'])).
% 1.06/1.31  thf('49', plain,
% 1.06/1.31      ((((sk_B) != (sk_B)))
% 1.06/1.31         <= (~ (((sk_B) = (k1_xboole_0))) & ~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['47', '48'])).
% 1.06/1.31  thf('50', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) | (((sk_B) = (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('simplify', [status(thm)], ['49'])).
% 1.06/1.31  thf('51', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('sat_resolution*', [status(thm)], ['38', '40', '50'])).
% 1.06/1.31  thf('52', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['37', '51'])).
% 1.06/1.31  thf('53', plain, ((((sk_C_2) = (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.06/1.31      inference('simplify_reflect-', [status(thm)], ['33', '52'])).
% 1.06/1.31  thf('54', plain,
% 1.06/1.31      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('split', [status(esa)], ['43'])).
% 1.06/1.31  thf('55', plain,
% 1.06/1.31      (((((sk_C_2) != (sk_C_2)) | ((sk_B) = (k1_xboole_0))))
% 1.06/1.31         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['53', '54'])).
% 1.06/1.31  thf('56', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['55'])).
% 1.06/1.31  thf(idempotence_k3_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.06/1.31  thf('57', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.06/1.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.06/1.31  thf(t4_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.06/1.31            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.06/1.31       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.06/1.31            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.06/1.31  thf('58', plain,
% 1.06/1.31      (![X8 : $i, X9 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ X8 @ X9)
% 1.06/1.31          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.06/1.31      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.06/1.31  thf('59', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r2_hidden @ (sk_C_1 @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['57', '58'])).
% 1.06/1.31  thf('60', plain,
% 1.06/1.31      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 1.06/1.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.06/1.31  thf('61', plain,
% 1.06/1.31      (![X64 : $i, X65 : $i]:
% 1.06/1.31         (((X65) = (k1_tarski @ X64))
% 1.06/1.31          | ((X65) = (k1_xboole_0))
% 1.06/1.31          | ~ (r1_tarski @ X65 @ (k1_tarski @ X64)))),
% 1.06/1.31      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.06/1.31  thf('62', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 1.06/1.31          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.31  thf('63', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.06/1.31      inference('sup+', [status(thm)], ['22', '23'])).
% 1.06/1.31  thf('64', plain,
% 1.06/1.31      (![X29 : $i, X30 : $i]:
% 1.06/1.31         ((k3_xboole_0 @ X29 @ X30)
% 1.06/1.31           = (k5_xboole_0 @ X29 @ 
% 1.06/1.31              (k5_xboole_0 @ X30 @ (k2_xboole_0 @ X29 @ X30))))),
% 1.06/1.31      inference('demod', [status(thm)], ['13', '14'])).
% 1.06/1.31  thf('65', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((k3_xboole_0 @ X0 @ k1_xboole_0)
% 1.06/1.31           = (k5_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['63', '64'])).
% 1.06/1.31  thf('66', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.06/1.31      inference('demod', [status(thm)], ['21', '24'])).
% 1.06/1.31  thf('67', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 1.06/1.31           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['65', '66'])).
% 1.06/1.31  thf('68', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0)
% 1.06/1.31            = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))
% 1.06/1.31          | ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['62', '67'])).
% 1.06/1.31  thf('69', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 1.06/1.31      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.06/1.31  thf('70', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (((k2_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 1.06/1.31          | ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 1.06/1.31      inference('demod', [status(thm)], ['68', '69'])).
% 1.06/1.31  thf('71', plain,
% 1.06/1.31      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.06/1.31      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.06/1.31  thf(l1_zfmisc_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.06/1.31  thf('72', plain,
% 1.06/1.31      (![X59 : $i, X60 : $i]:
% 1.06/1.31         ((r2_hidden @ X59 @ X60) | ~ (r1_tarski @ (k1_tarski @ X59) @ X60))),
% 1.06/1.31      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.31  thf('73', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (r2_hidden @ X1 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['71', '72'])).
% 1.06/1.31  thf('74', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r2_hidden @ X0 @ k1_xboole_0)
% 1.06/1.31          | ((k3_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['70', '73'])).
% 1.06/1.31  thf('75', plain,
% 1.06/1.31      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.06/1.31          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.06/1.31      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.06/1.31  thf('76', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 1.06/1.31          | (r2_hidden @ X0 @ k1_xboole_0)
% 1.06/1.31          | ~ (r1_xboole_0 @ (k1_tarski @ X0) @ k1_xboole_0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['74', '75'])).
% 1.06/1.31  thf(l27_zfmisc_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.06/1.31  thf('77', plain,
% 1.06/1.31      (![X62 : $i, X63 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ (k1_tarski @ X62) @ X63) | (r2_hidden @ X62 @ X63))),
% 1.06/1.31      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.06/1.31  thf('78', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         ((r2_hidden @ X0 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 1.06/1.31      inference('clc', [status(thm)], ['76', '77'])).
% 1.06/1.31  thf('79', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.31          | (r2_hidden @ X0 @ k1_xboole_0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['59', '78'])).
% 1.06/1.31  thf('80', plain,
% 1.06/1.31      (![X59 : $i, X61 : $i]:
% 1.06/1.31         ((r1_tarski @ (k1_tarski @ X59) @ X61) | ~ (r2_hidden @ X59 @ X61))),
% 1.06/1.31      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.06/1.31  thf('81', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.31          | (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['79', '80'])).
% 1.06/1.31  thf('82', plain,
% 1.06/1.31      (![X65 : $i, X66 : $i]:
% 1.06/1.31         ((r1_tarski @ X65 @ (k1_tarski @ X66)) | ((X65) != (k1_xboole_0)))),
% 1.06/1.31      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 1.06/1.31  thf('83', plain,
% 1.06/1.31      (![X66 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X66))),
% 1.06/1.31      inference('simplify', [status(thm)], ['82'])).
% 1.06/1.31  thf(d10_xboole_0, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.31  thf('84', plain,
% 1.06/1.31      (![X12 : $i, X14 : $i]:
% 1.06/1.31         (((X12) = (X14))
% 1.06/1.31          | ~ (r1_tarski @ X14 @ X12)
% 1.06/1.31          | ~ (r1_tarski @ X12 @ X14))),
% 1.06/1.31      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.31  thf('85', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 1.06/1.31          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['83', '84'])).
% 1.06/1.31  thf('86', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.31          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['81', '85'])).
% 1.06/1.31  thf('87', plain,
% 1.06/1.31      ((![X0 : $i]:
% 1.06/1.31          ((r1_xboole_0 @ sk_B @ k1_xboole_0)
% 1.06/1.31           | ((k1_tarski @ X0) = (k1_xboole_0))))
% 1.06/1.31         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('sup+', [status(thm)], ['56', '86'])).
% 1.06/1.31  thf('88', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['55'])).
% 1.06/1.31  thf('89', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['55'])).
% 1.06/1.31  thf('90', plain,
% 1.06/1.31      ((![X0 : $i]: ((r1_xboole_0 @ sk_B @ sk_B) | ((k1_tarski @ X0) = (sk_B))))
% 1.06/1.31         <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('demod', [status(thm)], ['87', '88', '89'])).
% 1.06/1.31  thf('91', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.31          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['81', '85'])).
% 1.06/1.31  thf(d3_tarski, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.31       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.31  thf('92', plain,
% 1.06/1.31      (![X3 : $i, X5 : $i]:
% 1.06/1.31         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.06/1.31      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.31  thf('93', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.06/1.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.06/1.31  thf('94', plain,
% 1.06/1.31      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.06/1.31          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.06/1.31      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.06/1.31  thf('95', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['93', '94'])).
% 1.06/1.31  thf('96', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['92', '95'])).
% 1.06/1.31  thf('97', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k1_tarski @ X1) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['91', '96'])).
% 1.06/1.31  thf('98', plain,
% 1.06/1.31      ((((sk_B) != (k1_tarski @ sk_A))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('split', [status(esa)], ['43'])).
% 1.06/1.31  thf('99', plain,
% 1.06/1.31      ((![X0 : $i]:
% 1.06/1.31          (((sk_B) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0)))
% 1.06/1.31         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['97', '98'])).
% 1.06/1.31  thf('100', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['46'])).
% 1.06/1.31  thf('101', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['46'])).
% 1.06/1.31  thf('102', plain,
% 1.06/1.31      ((![X0 : $i]: (((sk_B) != (sk_B)) | (r1_tarski @ sk_B @ X0)))
% 1.06/1.31         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('demod', [status(thm)], ['99', '100', '101'])).
% 1.06/1.31  thf('103', plain,
% 1.06/1.31      ((![X0 : $i]: (r1_tarski @ sk_B @ X0))
% 1.06/1.31         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['102'])).
% 1.06/1.31  thf(t12_xboole_1, axiom,
% 1.06/1.31    (![A:$i,B:$i]:
% 1.06/1.31     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.06/1.31  thf('104', plain,
% 1.06/1.31      (![X15 : $i, X16 : $i]:
% 1.06/1.31         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.06/1.31      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.31  thf('105', plain,
% 1.06/1.31      ((![X0 : $i]: ((k2_xboole_0 @ sk_B @ X0) = (X0)))
% 1.06/1.31         <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['103', '104'])).
% 1.06/1.31  thf('106', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['37', '51'])).
% 1.06/1.31  thf('107', plain,
% 1.06/1.31      ((((sk_C_2) != (sk_C_2))) <= (~ (((sk_B) = (k1_tarski @ sk_A))))),
% 1.06/1.31      inference('sup-', [status(thm)], ['105', '106'])).
% 1.06/1.31  thf('108', plain, ((((sk_B) = (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('simplify', [status(thm)], ['107'])).
% 1.06/1.31  thf('109', plain,
% 1.06/1.31      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B) = (k1_tarski @ sk_A)))),
% 1.06/1.31      inference('split', [status(esa)], ['43'])).
% 1.06/1.31  thf('110', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.06/1.31      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 1.06/1.31  thf('111', plain,
% 1.06/1.31      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ sk_B) | ((k1_tarski @ X0) = (sk_B)))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['90', '110'])).
% 1.06/1.31  thf('112', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('113', plain,
% 1.06/1.31      ((((sk_B) = (k2_xboole_0 @ sk_B @ sk_C_2)) | (r1_xboole_0 @ sk_B @ sk_B))),
% 1.06/1.31      inference('sup+', [status(thm)], ['111', '112'])).
% 1.06/1.31  thf('114', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.31  thf('115', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.06/1.31      inference('demod', [status(thm)], ['2', '3'])).
% 1.06/1.31  thf('116', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B @ sk_C_2)) = (sk_A))),
% 1.06/1.31      inference('sup+', [status(thm)], ['114', '115'])).
% 1.06/1.31  thf('117', plain,
% 1.06/1.31      ((((k3_tarski @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_B @ sk_B))),
% 1.06/1.31      inference('sup+', [status(thm)], ['113', '116'])).
% 1.06/1.31  thf('118', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r1_xboole_0 @ X0 @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['92', '95'])).
% 1.06/1.31  thf('119', plain,
% 1.06/1.31      (![X0 : $i]: (((k3_tarski @ sk_B) = (sk_A)) | (r1_tarski @ sk_B @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['117', '118'])).
% 1.06/1.31  thf('120', plain,
% 1.06/1.31      (![X15 : $i, X16 : $i]:
% 1.06/1.31         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.06/1.31      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.31  thf('121', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (((k3_tarski @ sk_B) = (sk_A)) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['119', '120'])).
% 1.06/1.31  thf('122', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['37', '51'])).
% 1.06/1.31  thf('123', plain, ((((sk_C_2) != (sk_C_2)) | ((k3_tarski @ sk_B) = (sk_A)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['121', '122'])).
% 1.06/1.31  thf('124', plain, (((k3_tarski @ sk_B) = (sk_A))),
% 1.06/1.31      inference('simplify', [status(thm)], ['123'])).
% 1.06/1.31  thf('125', plain,
% 1.06/1.31      (((k1_tarski @ (k3_tarski @ sk_B)) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('demod', [status(thm)], ['5', '124'])).
% 1.06/1.31  thf('126', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)
% 1.06/1.31          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['81', '85'])).
% 1.06/1.31  thf('127', plain,
% 1.06/1.31      (![X3 : $i, X5 : $i]:
% 1.06/1.31         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 1.06/1.31      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.31  thf('128', plain,
% 1.06/1.31      (![X8 : $i, X10 : $i, X11 : $i]:
% 1.06/1.31         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 1.06/1.31          | ~ (r1_xboole_0 @ X8 @ X11))),
% 1.06/1.31      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.06/1.31  thf('129', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.31         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.06/1.31          | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['127', '128'])).
% 1.06/1.31  thf('130', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k1_tarski @ X1) = (k1_xboole_0))
% 1.06/1.31          | (r1_tarski @ (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 1.06/1.31      inference('sup-', [status(thm)], ['126', '129'])).
% 1.06/1.31  thf('131', plain, (![X7 : $i]: ((k3_xboole_0 @ X7 @ X7) = (X7))),
% 1.06/1.31      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.06/1.31  thf('132', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k1_tarski @ X1) = (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.06/1.31      inference('demod', [status(thm)], ['130', '131'])).
% 1.06/1.31  thf('133', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['55'])).
% 1.06/1.31  thf('134', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.06/1.31      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 1.06/1.31  thf('135', plain, (((sk_B) = (k1_xboole_0))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 1.06/1.31  thf('136', plain, (((sk_B) = (k1_xboole_0))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['133', '134'])).
% 1.06/1.31  thf('137', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k1_tarski @ X1) = (sk_B)) | (r1_tarski @ sk_B @ X0))),
% 1.06/1.31      inference('demod', [status(thm)], ['132', '135', '136'])).
% 1.06/1.31  thf('138', plain,
% 1.06/1.31      (![X15 : $i, X16 : $i]:
% 1.06/1.31         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 1.06/1.31      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.06/1.31  thf('139', plain,
% 1.06/1.31      (![X0 : $i, X1 : $i]:
% 1.06/1.31         (((k1_tarski @ X1) = (sk_B)) | ((k2_xboole_0 @ sk_B @ X0) = (X0)))),
% 1.06/1.31      inference('sup-', [status(thm)], ['137', '138'])).
% 1.06/1.31  thf('140', plain,
% 1.06/1.31      (![X0 : $i]:
% 1.06/1.31         (((k1_tarski @ (k3_tarski @ sk_B)) = (sk_C_2))
% 1.06/1.31          | ((k1_tarski @ X0) = (sk_B)))),
% 1.06/1.31      inference('sup+', [status(thm)], ['125', '139'])).
% 1.06/1.31  thf('141', plain, (((sk_C_2) != (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['37', '51'])).
% 1.06/1.31  thf('142', plain,
% 1.06/1.31      (((k1_tarski @ (k3_tarski @ sk_B)) = (k2_xboole_0 @ sk_B @ sk_C_2))),
% 1.06/1.31      inference('demod', [status(thm)], ['5', '124'])).
% 1.06/1.31  thf('143', plain, (((sk_C_2) != (k1_tarski @ (k3_tarski @ sk_B)))),
% 1.06/1.31      inference('demod', [status(thm)], ['141', '142'])).
% 1.06/1.31  thf('144', plain, (![X0 : $i]: ((k1_tarski @ X0) = (sk_B))),
% 1.06/1.31      inference('simplify_reflect-', [status(thm)], ['140', '143'])).
% 1.06/1.31  thf('145', plain, (![X0 : $i]: ((k3_tarski @ sk_B) = (X0))),
% 1.06/1.31      inference('demod', [status(thm)], ['4', '144'])).
% 1.06/1.31  thf('146', plain, (![X0 : $i]: ((k3_tarski @ sk_B) = (X0))),
% 1.06/1.31      inference('demod', [status(thm)], ['4', '144'])).
% 1.06/1.31  thf('147', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 1.06/1.31      inference('sup+', [status(thm)], ['145', '146'])).
% 1.06/1.31  thf('148', plain,
% 1.06/1.31      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('split', [status(esa)], ['43'])).
% 1.06/1.31  thf('149', plain,
% 1.06/1.31      ((((sk_B) = (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('simplify', [status(thm)], ['55'])).
% 1.06/1.31  thf('150', plain,
% 1.06/1.31      ((((sk_C_2) != (sk_B))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 1.06/1.31      inference('demod', [status(thm)], ['148', '149'])).
% 1.06/1.31  thf('151', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 1.06/1.31      inference('sat_resolution*', [status(thm)], ['108', '109'])).
% 1.06/1.31  thf('152', plain, (((sk_C_2) != (sk_B))),
% 1.06/1.31      inference('simpl_trail', [status(thm)], ['150', '151'])).
% 1.06/1.31  thf('153', plain, (![X0 : $i]: ((X0) != (sk_B))),
% 1.06/1.31      inference('sup-', [status(thm)], ['147', '152'])).
% 1.06/1.31  thf('154', plain, ($false), inference('simplify', [status(thm)], ['153'])).
% 1.06/1.31  
% 1.06/1.31  % SZS output end Refutation
% 1.06/1.31  
% 1.06/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
