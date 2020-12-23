%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t8aH9rAk7x

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:33 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 293 expanded)
%              Number of leaves         :   21 (  96 expanded)
%              Depth                    :   22
%              Number of atoms          :  872 (2451 expanded)
%              Number of equality atoms :   62 ( 177 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

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

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X32: $i,X33: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X32 ) @ X33 )
      | ( r2_hidden @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('19',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','23'])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ( ( k3_xboole_0 @ X8 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('46',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('47',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('48',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('55',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) )
      = ( k4_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('58',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['43','61'])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('66',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('71',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('72',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ X13 )
      | ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('80',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ X17 @ X18 )
      | ( ( k4_xboole_0 @ X17 @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('86',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_xboole_0 @ X20 @ X21 )
        = X20 )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['26','89','90'])).

thf('92',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('94',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.t8aH9rAk7x
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 962 iterations in 0.434s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.71/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.71/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.90  thf(t48_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (![X24 : $i, X25 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.71/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      (![X24 : $i, X25 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.71/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['0', '1'])).
% 0.71/0.90  thf(t47_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.71/0.90           = (k4_xboole_0 @ X22 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k4_xboole_0 @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['2', '3'])).
% 0.71/0.90  thf(l27_zfmisc_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X32 : $i, X33 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 0.71/0.90      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.71/0.90  thf(d7_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.71/0.90       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.71/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r2_hidden @ X1 @ X0)
% 0.71/0.90          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0))
% 0.71/0.90          | (r2_hidden @ X1 @ (k4_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.71/0.90  thf(t3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.71/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.71/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.71/0.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X14))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.90  thf(d5_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.71/0.90       ( ![D:$i]:
% 0.71/0.90         ( ( r2_hidden @ D @ C ) <=>
% 0.71/0.90           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X6 @ X5)
% 0.71/0.90          | ~ (r2_hidden @ X6 @ X4)
% 0.71/0.90          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X6 @ X4)
% 0.71/0.90          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.71/0.90  thf('13', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.71/0.90          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['10', '12'])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.71/0.90          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['9', '13'])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.71/0.90      inference('simplify', [status(thm)], ['14'])).
% 0.71/0.90  thf(symmetry_r1_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X11 : $i, X12 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X11 @ X12) | ~ (r1_xboole_0 @ X12 @ X11))),
% 0.71/0.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X32 : $i, X33 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ (k1_tarski @ X32) @ X33) | (r2_hidden @ X32 @ X33))),
% 0.71/0.90      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.71/0.90  thf(t58_zfmisc_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.71/0.90       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i]:
% 0.71/0.90        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.71/0.90          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.71/0.90  thf('19', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.71/0.90      inference('sup-', [status(thm)], ['18', '19'])).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X15 @ X13)
% 0.71/0.90          | ~ (r2_hidden @ X15 @ X16)
% 0.71/0.90          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      (![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['17', '22'])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['8', '23'])).
% 0.71/0.90  thf('25', plain,
% 0.71/0.90      (![X24 : $i, X25 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.71/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('26', plain,
% 0.71/0.90      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.71/0.90         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.71/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf('27', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r2_hidden @ X1 @ X0)
% 0.71/0.90          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.71/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('28', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.71/0.90          | (r2_hidden @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['27', '28'])).
% 0.71/0.90  thf('30', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0))
% 0.71/0.90          | (r2_hidden @ X0 @ X1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['27', '28'])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.71/0.90           = (k4_xboole_0 @ X22 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      (![X24 : $i, X25 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.71/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['31', '32'])).
% 0.71/0.90  thf('34', plain,
% 0.71/0.90      (![X24 : $i, X25 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.71/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k3_xboole_0 @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['33', '34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (![X8 : $i, X10 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X8 @ X10)
% 0.71/0.90          | ((k3_xboole_0 @ X8 @ X10) != (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.71/0.90  thf('38', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['36', '37'])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.71/0.90          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['35', '38'])).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k1_xboole_0) != (k1_xboole_0))
% 0.71/0.90          | (r2_hidden @ X0 @ X1)
% 0.71/0.90          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['30', '39'])).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1)
% 0.71/0.90          | (r2_hidden @ X0 @ X1))),
% 0.71/0.90      inference('simplify', [status(thm)], ['40'])).
% 0.71/0.90  thf('42', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.71/0.90          | (r2_hidden @ X1 @ X0)
% 0.71/0.90          | (r2_hidden @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['29', '41'])).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.71/0.90      inference('simplify', [status(thm)], ['42'])).
% 0.71/0.90  thf('44', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.71/0.90      inference('sup-', [status(thm)], ['18', '19'])).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.71/0.90           = (k4_xboole_0 @ X22 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.71/0.90  thf('46', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.71/0.90      inference('sup-', [status(thm)], ['18', '19'])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X2 @ X3)
% 0.71/0.90          | (r2_hidden @ X2 @ X4)
% 0.71/0.90          | (r2_hidden @ X2 @ X5)
% 0.71/0.90          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.71/0.90         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.71/0.90          | (r2_hidden @ X2 @ X4)
% 0.71/0.90          | ~ (r2_hidden @ X2 @ X3))),
% 0.71/0.90      inference('simplify', [status(thm)], ['47'])).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ sk_A @ X0)
% 0.71/0.90          | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['46', '48'])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ X0))
% 0.71/0.90          | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['45', '49'])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X6 @ X4)
% 0.71/0.90          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.71/0.90  thf('52', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.71/0.90          | ~ (r2_hidden @ sk_A @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['50', '51'])).
% 0.71/0.90  thf('53', plain, ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['44', '52'])).
% 0.71/0.90  thf('54', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.71/0.90          | ~ (r2_hidden @ sk_A @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['50', '51'])).
% 0.71/0.90  thf('55', plain,
% 0.71/0.90      ((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_B)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['53', '54'])).
% 0.71/0.90  thf('56', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.71/0.90           = (k4_xboole_0 @ X22 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.71/0.90  thf('57', plain,
% 0.71/0.90      (![X22 : $i, X23 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23))
% 0.71/0.90           = (k4_xboole_0 @ X22 @ X23))),
% 0.71/0.90      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.71/0.90  thf('58', plain,
% 0.71/0.90      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X6 @ X4)
% 0.71/0.90          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['11'])).
% 0.71/0.90  thf('59', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['57', '58'])).
% 0.71/0.90  thf('60', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.71/0.90      inference('sup-', [status(thm)], ['56', '59'])).
% 0.71/0.90  thf('61', plain, (~ (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['55', '60'])).
% 0.71/0.90  thf('62', plain, ((r1_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B))),
% 0.71/0.90      inference('sup-', [status(thm)], ['43', '61'])).
% 0.71/0.90  thf('63', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.71/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.71/0.90  thf('64', plain,
% 0.71/0.90      (((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B))
% 0.71/0.90         = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['62', '63'])).
% 0.71/0.90  thf('65', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.71/0.90          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['35', '38'])).
% 0.71/0.90  thf('66', plain,
% 0.71/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.71/0.90        | (r1_xboole_0 @ 
% 0.71/0.90           (k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B)) @ 
% 0.71/0.90           k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['64', '65'])).
% 0.71/0.90  thf('67', plain,
% 0.71/0.90      (((k3_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_B))
% 0.71/0.90         = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['62', '63'])).
% 0.71/0.90  thf('68', plain,
% 0.71/0.90      ((((k1_xboole_0) != (k1_xboole_0))
% 0.71/0.90        | (r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['66', '67'])).
% 0.71/0.90  thf('69', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.71/0.90      inference('simplify', [status(thm)], ['68'])).
% 0.71/0.90  thf('70', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.90  thf('71', plain,
% 0.71/0.90      (![X13 : $i, X14 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X13 @ X14) | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.90  thf('72', plain,
% 0.71/0.90      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X15 @ X13)
% 0.71/0.90          | ~ (r2_hidden @ X15 @ X16)
% 0.71/0.90          | ~ (r1_xboole_0 @ X13 @ X16))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.71/0.90  thf('73', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X0 @ X1)
% 0.71/0.90          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.71/0.90          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.71/0.90      inference('sup-', [status(thm)], ['71', '72'])).
% 0.71/0.90  thf('74', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((r1_xboole_0 @ X0 @ X1)
% 0.71/0.90          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.71/0.90          | (r1_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['70', '73'])).
% 0.71/0.90  thf('75', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('simplify', [status(thm)], ['74'])).
% 0.71/0.90  thf('76', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.71/0.90      inference('sup-', [status(thm)], ['69', '75'])).
% 0.71/0.90  thf('77', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X8 @ X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X8 @ X9))),
% 0.71/0.90      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.71/0.90  thf('78', plain,
% 0.71/0.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['76', '77'])).
% 0.71/0.90  thf('79', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('80', plain,
% 0.71/0.90      (![X24 : $i, X25 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 0.71/0.90           = (k3_xboole_0 @ X24 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf(l32_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.90  thf('81', plain,
% 0.71/0.90      (![X17 : $i, X18 : $i]:
% 0.71/0.90         ((r1_tarski @ X17 @ X18)
% 0.71/0.90          | ((k4_xboole_0 @ X17 @ X18) != (k1_xboole_0)))),
% 0.71/0.90      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.71/0.90  thf('82', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.71/0.90          | (r1_tarski @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['80', '81'])).
% 0.71/0.90  thf('83', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0))
% 0.71/0.90          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['79', '82'])).
% 0.71/0.90  thf('84', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (((k1_xboole_0) != (k1_xboole_0))
% 0.71/0.90          | (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['78', '83'])).
% 0.71/0.90  thf('85', plain,
% 0.71/0.90      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('simplify', [status(thm)], ['84'])).
% 0.71/0.90  thf(t28_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.90  thf('86', plain,
% 0.71/0.90      (![X20 : $i, X21 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X20 @ X21) = (X20)) | ~ (r1_tarski @ X20 @ X21))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('87', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['85', '86'])).
% 0.71/0.90  thf('88', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]:
% 0.71/0.90         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.71/0.90           = (k4_xboole_0 @ X1 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['2', '3'])).
% 0.71/0.90  thf('89', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['87', '88'])).
% 0.71/0.90  thf('90', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('91', plain,
% 0.71/0.90      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.71/0.90      inference('demod', [status(thm)], ['26', '89', '90'])).
% 0.71/0.90  thf('92', plain,
% 0.71/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('93', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('94', plain,
% 0.71/0.90      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.71/0.90      inference('demod', [status(thm)], ['92', '93'])).
% 0.71/0.90  thf('95', plain, ($false),
% 0.71/0.90      inference('simplify_reflect-', [status(thm)], ['91', '94'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
