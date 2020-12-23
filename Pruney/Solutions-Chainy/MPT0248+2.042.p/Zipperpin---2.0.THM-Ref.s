%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CvGCOkgrql

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:23 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  172 (1492 expanded)
%              Number of leaves         :   39 ( 456 expanded)
%              Depth                    :   31
%              Number of atoms          : 1016 (13700 expanded)
%              Number of equality atoms :  138 (2265 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('2',plain,(
    ! [X72: $i,X73: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X72 ) @ X73 )
      | ( r2_hidden @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X32: $i,X33: $i] :
      ( r1_tarski @ X32 @ ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
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

thf('9',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('14',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X69 ) @ X71 )
      | ~ ( r2_hidden @ X69 @ X71 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('19',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X31: $i] :
      ( ( k5_xboole_0 @ X31 @ k1_xboole_0 )
      = X31 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('28',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('29',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('31',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['27','28'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('35',plain,(
    ! [X34: $i,X36: $i] :
      ( ( r1_xboole_0 @ X34 @ X36 )
      | ( ( k4_xboole_0 @ X34 @ X36 )
       != X34 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('36',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','38'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_xboole_0 @ X25 @ X24 )
        = X24 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','42'])).

thf('44',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['44'])).

thf('46',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('47',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( sk_C_2
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('50',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('51',plain,(
    ! [X17: $i,X19: $i] :
      ( ( X17 = X19 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k1_tarski @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_2 != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('56',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('59',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['44'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','61'])).

thf('63',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['46','48','62'])).

thf('64',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['43','64'])).

thf('66',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['19','65'])).

thf('67',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('68',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['19','65'])).

thf('69',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['19','65'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('70',plain,(
    ! [X41: $i] :
      ( ( k2_tarski @ X41 @ X41 )
      = ( k1_tarski @ X41 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('71',plain,(
    ! [X74: $i,X75: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X74 @ X75 ) )
      = ( k2_xboole_0 @ X74 @ X75 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( X17 != X18 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('74',plain,(
    ! [X18: $i] :
      ( r1_tarski @ X18 @ X18 ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_xboole_0 @ X25 @ X24 )
        = X24 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['72','76'])).

thf('78',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['69','77'])).

thf('79',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','78'])).

thf('80',plain,(
    ! [X72: $i,X73: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X72 ) @ X73 )
      | ( r2_hidden @ X72 @ X73 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X69: $i,X71: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X69 ) @ X71 )
      | ~ ( r2_hidden @ X69 @ X71 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','78'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_xboole_0 @ X25 @ X24 )
        = X24 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_B_1 = sk_C_2 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['67','87'])).

thf('89',plain,(
    sk_C_2
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['45','63'])).

thf('90',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference(clc,[status(thm)],['19','65'])).

thf('91',plain,(
    sk_C_2 != sk_B_1 ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X6: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('94',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['96','97'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('99',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('100',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['98','99'])).

thf('101',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','66'])).

thf('102',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','38'])).

thf('103',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_xboole_0 @ X29 @ X30 )
        = X29 )
      | ~ ( r1_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k5_xboole_0 @ X20 @ X21 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X20 @ X21 ) @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('109',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ( k5_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['100','101','109'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('111',plain,(
    ! [X40: $i] :
      ( ( k5_xboole_0 @ X40 @ X40 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('112',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ X39 )
      = ( k5_xboole_0 @ X37 @ ( k5_xboole_0 @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,
    ( sk_C_2
    = ( k5_xboole_0 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X11: $i] :
      ( ( k3_xboole_0 @ X11 @ X11 )
      = X11 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('118',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('121',plain,(
    ! [X40: $i] :
      ( ( k5_xboole_0 @ X40 @ X40 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['120','121'])).

thf('123',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['116','119','122'])).

thf('124',plain,
    ( ( sk_C_2 != k1_xboole_0 )
   <= ( sk_C_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['54'])).

thf('125',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['43','64'])).

thf('127',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['54'])).

thf('129',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['127','128'])).

thf('130',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['124','129'])).

thf('131',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['123','130'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CvGCOkgrql
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:37:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.66/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.83  % Solved by: fo/fo7.sh
% 0.66/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.83  % done 1167 iterations in 0.370s
% 0.66/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.83  % SZS output start Refutation
% 0.66/0.83  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.66/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.83  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.66/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.66/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.83  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.66/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.66/0.83  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.66/0.83  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.66/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.66/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.83  thf(t43_zfmisc_1, conjecture,
% 0.66/0.83    (![A:$i,B:$i,C:$i]:
% 0.66/0.83     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.66/0.83          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.66/0.83          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.66/0.83          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.66/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.66/0.83        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.66/0.83             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.66/0.83             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 0.66/0.83             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.66/0.83    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 0.66/0.83  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(d1_xboole_0, axiom,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.66/0.83  thf('1', plain,
% 0.66/0.83      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.66/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.66/0.83  thf(l27_zfmisc_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.66/0.83  thf('2', plain,
% 0.66/0.83      (![X72 : $i, X73 : $i]:
% 0.66/0.83         ((r1_xboole_0 @ (k1_tarski @ X72) @ X73) | (r2_hidden @ X72 @ X73))),
% 0.66/0.83      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.66/0.83  thf('3', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(t7_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.83  thf('4', plain,
% 0.66/0.83      (![X32 : $i, X33 : $i]: (r1_tarski @ X32 @ (k2_xboole_0 @ X32 @ X33))),
% 0.66/0.83      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.66/0.83  thf('5', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.66/0.83      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.83  thf(t28_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.83  thf('6', plain,
% 0.66/0.83      (![X29 : $i, X30 : $i]:
% 0.66/0.83         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 0.66/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.83  thf('7', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['5', '6'])).
% 0.66/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.66/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.66/0.83  thf('8', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.66/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.66/0.83  thf(t4_xboole_0, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.66/0.83            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.66/0.83       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.66/0.83            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.66/0.83  thf('9', plain,
% 0.66/0.83      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.66/0.83          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.66/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.66/0.83  thf('10', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.83          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['8', '9'])).
% 0.66/0.83  thf('11', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.66/0.83          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['7', '10'])).
% 0.66/0.83  thf('12', plain,
% 0.66/0.83      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['2', '11'])).
% 0.66/0.83  thf('13', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['1', '12'])).
% 0.66/0.83  thf(l1_zfmisc_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.66/0.83  thf('14', plain,
% 0.66/0.83      (![X69 : $i, X71 : $i]:
% 0.66/0.83         ((r1_tarski @ (k1_tarski @ X69) @ X71) | ~ (r2_hidden @ X69 @ X71))),
% 0.66/0.83      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.66/0.83  thf('15', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.83  thf(d10_xboole_0, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.66/0.83  thf('16', plain,
% 0.66/0.83      (![X17 : $i, X19 : $i]:
% 0.66/0.83         (((X17) = (X19))
% 0.66/0.83          | ~ (r1_tarski @ X19 @ X17)
% 0.66/0.83          | ~ (r1_tarski @ X17 @ X19))),
% 0.66/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.83  thf('17', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1)
% 0.66/0.83        | ~ (r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))
% 0.66/0.83        | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.66/0.83  thf('18', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.66/0.83      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.83  thf('19', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('demod', [status(thm)], ['17', '18'])).
% 0.66/0.83  thf('20', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf(l13_xboole_0, axiom,
% 0.66/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.66/0.83  thf('21', plain,
% 0.66/0.83      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.66/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.83  thf(d3_tarski, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.83  thf('22', plain,
% 0.66/0.83      (![X8 : $i, X10 : $i]:
% 0.66/0.83         ((r1_tarski @ X8 @ X10) | (r2_hidden @ (sk_C @ X10 @ X8) @ X8))),
% 0.66/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.83  thf(t100_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.83  thf('23', plain,
% 0.66/0.83      (![X22 : $i, X23 : $i]:
% 0.66/0.83         ((k4_xboole_0 @ X22 @ X23)
% 0.66/0.83           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.66/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.83  thf(commutativity_k5_xboole_0, axiom,
% 0.66/0.83    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.66/0.83  thf('24', plain,
% 0.66/0.83      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 0.66/0.83      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.66/0.83  thf(t5_boole, axiom,
% 0.66/0.83    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.83  thf('25', plain, (![X31 : $i]: ((k5_xboole_0 @ X31 @ k1_xboole_0) = (X31))),
% 0.66/0.83      inference('cnf', [status(esa)], [t5_boole])).
% 0.66/0.83  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['24', '25'])).
% 0.66/0.83  thf('27', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['23', '26'])).
% 0.66/0.83  thf(idempotence_k3_xboole_0, axiom,
% 0.66/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.66/0.83  thf('28', plain, (![X11 : $i]: ((k3_xboole_0 @ X11 @ X11) = (X11))),
% 0.66/0.83      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.66/0.83  thf('29', plain,
% 0.66/0.83      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['27', '28'])).
% 0.66/0.83  thf('30', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['23', '26'])).
% 0.66/0.83  thf('31', plain,
% 0.66/0.83      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.66/0.83          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.66/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.66/0.83  thf('32', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.66/0.83          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.66/0.83  thf('33', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X0 @ k1_xboole_0)
% 0.66/0.83          | ~ (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['29', '32'])).
% 0.66/0.83  thf('34', plain,
% 0.66/0.83      (((k4_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['27', '28'])).
% 0.66/0.83  thf(t83_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.66/0.83  thf('35', plain,
% 0.66/0.83      (![X34 : $i, X36 : $i]:
% 0.66/0.83         ((r1_xboole_0 @ X34 @ X36) | ((k4_xboole_0 @ X34 @ X36) != (X34)))),
% 0.66/0.83      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.66/0.83  thf('36', plain,
% 0.66/0.83      ((((k1_xboole_0) != (k1_xboole_0))
% 0.66/0.83        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.66/0.83  thf('37', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.66/0.83      inference('simplify', [status(thm)], ['36'])).
% 0.66/0.83  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.66/0.83      inference('demod', [status(thm)], ['33', '37'])).
% 0.66/0.83  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.66/0.83      inference('sup-', [status(thm)], ['22', '38'])).
% 0.66/0.83  thf(t12_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.66/0.83  thf('40', plain,
% 0.66/0.83      (![X24 : $i, X25 : $i]:
% 0.66/0.83         (((k2_xboole_0 @ X25 @ X24) = (X24)) | ~ (r1_tarski @ X25 @ X24))),
% 0.66/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.66/0.83  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.83  thf('42', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['21', '41'])).
% 0.66/0.83  thf('43', plain,
% 0.66/0.83      ((((k1_tarski @ sk_A) = (sk_C_2)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.66/0.83      inference('sup+', [status(thm)], ['20', '42'])).
% 0.66/0.83  thf('44', plain,
% 0.66/0.83      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('45', plain,
% 0.66/0.83      ((((sk_C_2) != (k1_tarski @ sk_A)))
% 0.66/0.83         <= (~ (((sk_C_2) = (k1_tarski @ sk_A))))),
% 0.66/0.83      inference('split', [status(esa)], ['44'])).
% 0.66/0.83  thf('46', plain,
% 0.66/0.83      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.66/0.83      inference('split', [status(esa)], ['44'])).
% 0.66/0.83  thf('47', plain,
% 0.66/0.83      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('48', plain,
% 0.66/0.83      (~ (((sk_C_2) = (k1_tarski @ sk_A))) | 
% 0.66/0.83       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('split', [status(esa)], ['47'])).
% 0.66/0.83  thf('49', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1) | (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.66/0.83      inference('sup-', [status(thm)], ['13', '14'])).
% 0.66/0.83  thf('50', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.66/0.83      inference('sup+', [status(thm)], ['3', '4'])).
% 0.66/0.83  thf('51', plain,
% 0.66/0.83      (![X17 : $i, X19 : $i]:
% 0.66/0.83         (((X17) = (X19))
% 0.66/0.83          | ~ (r1_tarski @ X19 @ X17)
% 0.66/0.83          | ~ (r1_tarski @ X17 @ X19))),
% 0.66/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.83  thf('52', plain,
% 0.66/0.83      ((~ (r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.66/0.83        | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['50', '51'])).
% 0.66/0.83  thf('53', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1) | ((k1_tarski @ sk_A) = (sk_B_1)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['49', '52'])).
% 0.66/0.83  thf('54', plain,
% 0.66/0.83      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_2) != (k1_xboole_0)))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('55', plain,
% 0.66/0.83      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 0.66/0.83         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.66/0.83      inference('split', [status(esa)], ['54'])).
% 0.66/0.83  thf('56', plain,
% 0.66/0.83      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 0.66/0.83         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.66/0.83      inference('sup-', [status(thm)], ['53', '55'])).
% 0.66/0.83  thf('57', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.66/0.83      inference('simplify', [status(thm)], ['56'])).
% 0.66/0.83  thf('58', plain,
% 0.66/0.83      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.66/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.83  thf('59', plain,
% 0.66/0.83      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.66/0.83      inference('split', [status(esa)], ['44'])).
% 0.66/0.83  thf('60', plain,
% 0.66/0.83      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.66/0.83         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.66/0.83      inference('sup-', [status(thm)], ['58', '59'])).
% 0.66/0.83  thf('61', plain,
% 0.66/0.83      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.66/0.83      inference('simplify', [status(thm)], ['60'])).
% 0.66/0.83  thf('62', plain,
% 0.66/0.83      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['57', '61'])).
% 0.66/0.83  thf('63', plain, (~ (((sk_C_2) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('sat_resolution*', [status(thm)], ['46', '48', '62'])).
% 0.66/0.83  thf('64', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.66/0.83      inference('simpl_trail', [status(thm)], ['45', '63'])).
% 0.66/0.83  thf('65', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.66/0.83      inference('simplify_reflect-', [status(thm)], ['43', '64'])).
% 0.66/0.83  thf('66', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.66/0.83      inference('clc', [status(thm)], ['19', '65'])).
% 0.66/0.83  thf('67', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('demod', [status(thm)], ['0', '66'])).
% 0.66/0.83  thf('68', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.66/0.83      inference('clc', [status(thm)], ['19', '65'])).
% 0.66/0.83  thf('69', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.66/0.83      inference('clc', [status(thm)], ['19', '65'])).
% 0.66/0.83  thf(t69_enumset1, axiom,
% 0.66/0.83    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.66/0.83  thf('70', plain,
% 0.66/0.83      (![X41 : $i]: ((k2_tarski @ X41 @ X41) = (k1_tarski @ X41))),
% 0.66/0.83      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.66/0.83  thf(l51_zfmisc_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.66/0.83  thf('71', plain,
% 0.66/0.83      (![X74 : $i, X75 : $i]:
% 0.66/0.83         ((k3_tarski @ (k2_tarski @ X74 @ X75)) = (k2_xboole_0 @ X74 @ X75))),
% 0.66/0.83      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.66/0.83  thf('72', plain,
% 0.66/0.83      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['70', '71'])).
% 0.66/0.83  thf('73', plain,
% 0.66/0.83      (![X17 : $i, X18 : $i]: ((r1_tarski @ X17 @ X18) | ((X17) != (X18)))),
% 0.66/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.66/0.83  thf('74', plain, (![X18 : $i]: (r1_tarski @ X18 @ X18)),
% 0.66/0.83      inference('simplify', [status(thm)], ['73'])).
% 0.66/0.83  thf('75', plain,
% 0.66/0.83      (![X24 : $i, X25 : $i]:
% 0.66/0.83         (((k2_xboole_0 @ X25 @ X24) = (X24)) | ~ (r1_tarski @ X25 @ X24))),
% 0.66/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.66/0.83  thf('76', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['74', '75'])).
% 0.66/0.83  thf('77', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.66/0.83      inference('demod', [status(thm)], ['72', '76'])).
% 0.66/0.83  thf('78', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.66/0.83      inference('sup+', [status(thm)], ['69', '77'])).
% 0.66/0.83  thf('79', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.66/0.83      inference('demod', [status(thm)], ['68', '78'])).
% 0.66/0.83  thf('80', plain,
% 0.66/0.83      (![X72 : $i, X73 : $i]:
% 0.66/0.83         ((r1_xboole_0 @ (k1_tarski @ X72) @ X73) | (r2_hidden @ X72 @ X73))),
% 0.66/0.83      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.66/0.83  thf('81', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((r1_xboole_0 @ sk_B_1 @ X0) | (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['79', '80'])).
% 0.66/0.83  thf('82', plain,
% 0.66/0.83      (![X69 : $i, X71 : $i]:
% 0.66/0.83         ((r1_tarski @ (k1_tarski @ X69) @ X71) | ~ (r2_hidden @ X69 @ X71))),
% 0.66/0.83      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.66/0.83  thf('83', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((r1_xboole_0 @ sk_B_1 @ X0)
% 0.66/0.83          | (r1_tarski @ (k1_tarski @ (k3_tarski @ sk_B_1)) @ X0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['81', '82'])).
% 0.66/0.83  thf('84', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 0.66/0.83      inference('demod', [status(thm)], ['68', '78'])).
% 0.66/0.83  thf('85', plain,
% 0.66/0.83      (![X0 : $i]: ((r1_xboole_0 @ sk_B_1 @ X0) | (r1_tarski @ sk_B_1 @ X0))),
% 0.66/0.83      inference('demod', [status(thm)], ['83', '84'])).
% 0.66/0.83  thf('86', plain,
% 0.66/0.83      (![X24 : $i, X25 : $i]:
% 0.66/0.83         (((k2_xboole_0 @ X25 @ X24) = (X24)) | ~ (r1_tarski @ X25 @ X24))),
% 0.66/0.83      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.66/0.83  thf('87', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((r1_xboole_0 @ sk_B_1 @ X0) | ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['85', '86'])).
% 0.66/0.83  thf('88', plain, ((((sk_B_1) = (sk_C_2)) | (r1_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('sup+', [status(thm)], ['67', '87'])).
% 0.66/0.83  thf('89', plain, (((sk_C_2) != (k1_tarski @ sk_A))),
% 0.66/0.83      inference('simpl_trail', [status(thm)], ['45', '63'])).
% 0.66/0.83  thf('90', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.66/0.83      inference('clc', [status(thm)], ['19', '65'])).
% 0.66/0.83  thf('91', plain, (((sk_C_2) != (sk_B_1))),
% 0.66/0.83      inference('demod', [status(thm)], ['89', '90'])).
% 0.66/0.83  thf('92', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_2)),
% 0.66/0.83      inference('simplify_reflect-', [status(thm)], ['88', '91'])).
% 0.66/0.83  thf('93', plain,
% 0.66/0.83      (![X6 : $i]: ((v1_xboole_0 @ X6) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.66/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.66/0.83  thf('94', plain,
% 0.66/0.83      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.66/0.83         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 0.66/0.83          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.66/0.83      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.66/0.83  thf('95', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['93', '94'])).
% 0.66/0.83  thf('96', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('sup-', [status(thm)], ['92', '95'])).
% 0.66/0.83  thf('97', plain,
% 0.66/0.83      (![X12 : $i]: (((X12) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X12))),
% 0.66/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.66/0.83  thf('98', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['96', '97'])).
% 0.66/0.83  thf(l98_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i]:
% 0.66/0.83     ( ( k5_xboole_0 @ A @ B ) =
% 0.66/0.83       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.66/0.83  thf('99', plain,
% 0.66/0.83      (![X20 : $i, X21 : $i]:
% 0.66/0.83         ((k5_xboole_0 @ X20 @ X21)
% 0.66/0.83           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 0.66/0.83              (k3_xboole_0 @ X20 @ X21)))),
% 0.66/0.83      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.66/0.83  thf('100', plain,
% 0.66/0.83      (((k5_xboole_0 @ sk_B_1 @ sk_C_2)
% 0.66/0.83         = (k4_xboole_0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2) @ k1_xboole_0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['98', '99'])).
% 0.66/0.83  thf('101', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.66/0.83      inference('demod', [status(thm)], ['0', '66'])).
% 0.66/0.83  thf('102', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.66/0.83      inference('sup-', [status(thm)], ['22', '38'])).
% 0.66/0.83  thf('103', plain,
% 0.66/0.83      (![X29 : $i, X30 : $i]:
% 0.66/0.83         (((k3_xboole_0 @ X29 @ X30) = (X29)) | ~ (r1_tarski @ X29 @ X30))),
% 0.66/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.66/0.83  thf('104', plain,
% 0.66/0.83      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['102', '103'])).
% 0.66/0.83  thf('105', plain,
% 0.66/0.83      (![X20 : $i, X21 : $i]:
% 0.66/0.83         ((k5_xboole_0 @ X20 @ X21)
% 0.66/0.83           = (k4_xboole_0 @ (k2_xboole_0 @ X20 @ X21) @ 
% 0.66/0.83              (k3_xboole_0 @ X20 @ X21)))),
% 0.66/0.83      inference('cnf', [status(esa)], [l98_xboole_1])).
% 0.66/0.83  thf('106', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.66/0.83           = (k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['104', '105'])).
% 0.66/0.83  thf('107', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['24', '25'])).
% 0.66/0.83  thf('108', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.83      inference('sup-', [status(thm)], ['39', '40'])).
% 0.66/0.83  thf('109', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.83      inference('demod', [status(thm)], ['106', '107', '108'])).
% 0.66/0.83  thf('110', plain, (((k5_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 0.66/0.83      inference('demod', [status(thm)], ['100', '101', '109'])).
% 0.66/0.83  thf(t92_xboole_1, axiom,
% 0.66/0.83    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.66/0.83  thf('111', plain, (![X40 : $i]: ((k5_xboole_0 @ X40 @ X40) = (k1_xboole_0))),
% 0.66/0.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.66/0.83  thf(t91_xboole_1, axiom,
% 0.66/0.83    (![A:$i,B:$i,C:$i]:
% 0.66/0.83     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.66/0.83       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.66/0.83  thf('112', plain,
% 0.66/0.83      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.66/0.83         ((k5_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ X39)
% 0.66/0.83           = (k5_xboole_0 @ X37 @ (k5_xboole_0 @ X38 @ X39)))),
% 0.66/0.83      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.66/0.83  thf('113', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.66/0.83           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.83      inference('sup+', [status(thm)], ['111', '112'])).
% 0.66/0.83  thf('114', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['24', '25'])).
% 0.66/0.83  thf('115', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.66/0.83      inference('demod', [status(thm)], ['113', '114'])).
% 0.66/0.83  thf('116', plain, (((sk_C_2) = (k5_xboole_0 @ sk_B_1 @ sk_B_1))),
% 0.66/0.83      inference('sup+', [status(thm)], ['110', '115'])).
% 0.66/0.83  thf('117', plain, (![X11 : $i]: ((k3_xboole_0 @ X11 @ X11) = (X11))),
% 0.66/0.83      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.66/0.83  thf('118', plain,
% 0.66/0.83      (![X22 : $i, X23 : $i]:
% 0.66/0.83         ((k4_xboole_0 @ X22 @ X23)
% 0.66/0.83           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.66/0.83      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.66/0.83  thf('119', plain,
% 0.66/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['117', '118'])).
% 0.66/0.83  thf('120', plain,
% 0.66/0.83      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['117', '118'])).
% 0.66/0.83  thf('121', plain, (![X40 : $i]: ((k5_xboole_0 @ X40 @ X40) = (k1_xboole_0))),
% 0.66/0.83      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.66/0.83  thf('122', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.83      inference('sup+', [status(thm)], ['120', '121'])).
% 0.66/0.83  thf('123', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.66/0.83      inference('demod', [status(thm)], ['116', '119', '122'])).
% 0.66/0.83  thf('124', plain,
% 0.66/0.83      ((((sk_C_2) != (k1_xboole_0))) <= (~ (((sk_C_2) = (k1_xboole_0))))),
% 0.66/0.83      inference('split', [status(esa)], ['54'])).
% 0.66/0.83  thf('125', plain,
% 0.66/0.83      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 0.66/0.83      inference('simplify', [status(thm)], ['56'])).
% 0.66/0.83  thf('126', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.66/0.83      inference('simplify_reflect-', [status(thm)], ['43', '64'])).
% 0.66/0.83  thf('127', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('sup-', [status(thm)], ['125', '126'])).
% 0.66/0.83  thf('128', plain,
% 0.66/0.83      (~ (((sk_C_2) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.66/0.83      inference('split', [status(esa)], ['54'])).
% 0.66/0.83  thf('129', plain, (~ (((sk_C_2) = (k1_xboole_0)))),
% 0.66/0.83      inference('sat_resolution*', [status(thm)], ['127', '128'])).
% 0.66/0.83  thf('130', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.66/0.83      inference('simpl_trail', [status(thm)], ['124', '129'])).
% 0.66/0.83  thf('131', plain, ($false),
% 0.66/0.83      inference('simplify_reflect-', [status(thm)], ['123', '130'])).
% 0.66/0.83  
% 0.66/0.83  % SZS output end Refutation
% 0.66/0.83  
% 0.66/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
