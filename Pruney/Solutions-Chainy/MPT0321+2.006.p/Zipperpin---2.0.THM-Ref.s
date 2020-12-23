%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dgZZHYewBS

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:33 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  179 (1653 expanded)
%              Number of leaves         :   24 ( 534 expanded)
%              Depth                    :   28
%              Number of atoms          : 1458 (16579 expanded)
%              Number of equality atoms :  148 (2012 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t134_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = ( k2_zfmisc_1 @ C @ D ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( ( A = C )
            & ( B = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t134_zfmisc_1])).

thf('4',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('5',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X38 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X38 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ X1 @ sk_C ) @ ( k3_xboole_0 @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k2_xboole_0 @ X34 @ X36 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('10',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['9','12'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('15',plain,
    ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X38 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ ( k2_xboole_0 @ sk_D @ sk_B ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X38 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ X1 ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ X1 ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k3_xboole_0 @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('31',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','28','29','30','39'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t117_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) )
          | ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) )
        & ~ ( r1_tarski @ B @ C ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X32 @ X31 ) @ ( k2_zfmisc_1 @ X33 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) )
    | ( r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('54',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X38 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ sk_A @ X0 ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_D )
    = ( k2_zfmisc_1 @ sk_C @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('58',plain,(
    r1_tarski @ sk_A @ ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['46','56','57'])).

thf('59',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('63',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X10 @ ( k2_xboole_0 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['68','73'])).

thf('75',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_A )
      | ( ( k2_xboole_0 @ X0 @ sk_C )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_A )
    | ( ( k2_xboole_0 @ sk_C @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('79',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_A )
    | ( sk_C = sk_A ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( sk_A != sk_C )
   <= ( sk_A != sk_C ) ),
    inference(split,[status(esa)],['80'])).

thf('82',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X34 @ X36 ) @ X35 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X34 @ X35 ) @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('83',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X34: $i,X36: $i,X37: $i] :
      ( ( k2_zfmisc_1 @ X37 @ ( k2_xboole_0 @ X34 @ X36 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X37 @ X34 ) @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('88',plain,
    ( ( k2_zfmisc_1 @ sk_A @ ( k2_xboole_0 @ sk_D @ sk_B ) )
    = ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_A ) @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['88','93'])).

thf('95',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('96',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k3_xboole_0 @ X18 @ X19 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('97',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_A )
    = sk_C ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('99',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_D @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['94','97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('101',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('103',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( ( k2_xboole_0 @ sk_D @ sk_B )
      = sk_D ) ),
    inference('sup-',[status(thm)],['101','104'])).

thf('106',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['99','100'])).

thf('107',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ( sk_B = sk_D ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('111',plain,(
    ! [X26: $i,X27: $i] :
      ( r1_tarski @ X26 @ ( k2_xboole_0 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k4_xboole_0 @ X24 @ ( k4_xboole_0 @ X24 @ X25 ) )
      = ( k3_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X21: $i] :
      ( ( k4_xboole_0 @ X21 @ k1_xboole_0 )
      = X21 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('119',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X38 @ X40 ) @ ( k3_xboole_0 @ X39 @ X41 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X38 @ X39 ) @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_D @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['99','100'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('123',plain,
    ( sk_D
    = ( k3_xboole_0 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ sk_C @ sk_D )
      = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ ( k2_xboole_0 @ X0 @ sk_A ) ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['120','123'])).

thf('125',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_D )
    = ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_C @ sk_A ) @ sk_D ) ),
    inference('sup+',[status(thm)],['108','124'])).

thf('126',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('127',plain,
    ( ( k2_zfmisc_1 @ sk_C @ sk_D )
    = ( k2_zfmisc_1 @ sk_A @ sk_D ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X31 @ X32 ) @ ( k2_zfmisc_1 @ X31 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_A @ X0 ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('135',plain,(
    r1_tarski @ sk_B @ sk_D ),
    inference(demod,[status(thm)],['133','134'])).

thf('136',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['107','135'])).

thf('137',plain,
    ( ( sk_B != sk_D )
   <= ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('138',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B != sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    sk_B = sk_D ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( sk_A != sk_C )
    | ( sk_B != sk_D ) ),
    inference(split,[status(esa)],['80'])).

thf('141',plain,(
    sk_A != sk_C ),
    inference('sat_resolution*',[status(thm)],['139','140'])).

thf('142',plain,(
    sk_A != sk_C ),
    inference(simpl_trail,[status(thm)],['81','141'])).

thf('143',plain,(
    ~ ( r1_tarski @ sk_C @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['79','142'])).

thf('144',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('145',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 = k1_xboole_0 )
      | ( r1_tarski @ X32 @ X33 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X32 @ X31 ) @ ( k2_zfmisc_1 @ X33 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t117_zfmisc_1])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['147','148'])).

thf('150',plain,(
    sk_B = sk_D ),
    inference(demod,[status(thm)],['107','135'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,(
    r1_tarski @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['143','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dgZZHYewBS
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:33:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.16/4.39  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.16/4.39  % Solved by: fo/fo7.sh
% 4.16/4.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.16/4.39  % done 3632 iterations in 3.930s
% 4.16/4.39  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.16/4.39  % SZS output start Refutation
% 4.16/4.39  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.16/4.39  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.16/4.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.16/4.39  thf(sk_A_type, type, sk_A: $i).
% 4.16/4.39  thf(sk_D_type, type, sk_D: $i).
% 4.16/4.39  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.16/4.39  thf(sk_B_type, type, sk_B: $i).
% 4.16/4.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.16/4.39  thf(sk_C_type, type, sk_C: $i).
% 4.16/4.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.16/4.39  thf(d10_xboole_0, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.16/4.39  thf('0', plain,
% 4.16/4.39      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 4.16/4.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.39  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.16/4.39      inference('simplify', [status(thm)], ['0'])).
% 4.16/4.39  thf(t12_xboole_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.16/4.39  thf('2', plain,
% 4.16/4.39      (![X13 : $i, X14 : $i]:
% 4.16/4.39         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 4.16/4.39      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.16/4.39  thf('3', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['1', '2'])).
% 4.16/4.39  thf(t134_zfmisc_1, conjecture,
% 4.16/4.39    (![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.39     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 4.16/4.39       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.16/4.39         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 4.16/4.39  thf(zf_stmt_0, negated_conjecture,
% 4.16/4.39    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.39        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 4.16/4.39          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 4.16/4.39            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 4.16/4.39    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 4.16/4.39  thf('4', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf(t123_zfmisc_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i,D:$i]:
% 4.16/4.39     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 4.16/4.39       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 4.16/4.39  thf('5', plain,
% 4.16/4.39      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X38 @ X40) @ (k3_xboole_0 @ X39 @ X41))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X40 @ X41)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.16/4.39  thf('6', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 4.16/4.39              (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['4', '5'])).
% 4.16/4.39  thf('7', plain,
% 4.16/4.39      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X38 @ X40) @ (k3_xboole_0 @ X39 @ X41))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X40 @ X41)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.16/4.39  thf('8', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))
% 4.16/4.39           = (k2_zfmisc_1 @ (k3_xboole_0 @ X1 @ sk_C) @ 
% 4.16/4.39              (k3_xboole_0 @ X0 @ sk_D)))),
% 4.16/4.39      inference('demod', [status(thm)], ['6', '7'])).
% 4.16/4.39  thf(t120_zfmisc_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 4.16/4.39         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 4.16/4.39       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 4.16/4.39         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 4.16/4.39  thf('9', plain,
% 4.16/4.39      (![X34 : $i, X36 : $i, X37 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ X37 @ (k2_xboole_0 @ X34 @ X36))
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X37 @ X36)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.16/4.39  thf('10', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('11', plain,
% 4.16/4.39      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k2_xboole_0 @ X34 @ X36) @ X35)
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X36 @ X35)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.16/4.39  thf('12', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['10', '11'])).
% 4.16/4.39  thf('13', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)
% 4.16/4.39         = (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['9', '12'])).
% 4.16/4.39  thf(commutativity_k2_xboole_0, axiom,
% 4.16/4.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 4.16/4.39  thf('14', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.16/4.39  thf('15', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_B)
% 4.16/4.39         = (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['13', '14'])).
% 4.16/4.39  thf('16', plain,
% 4.16/4.39      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X38 @ X40) @ (k3_xboole_0 @ X39 @ X41))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X40 @ X41)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.16/4.39  thf('17', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ X1) @ 
% 4.16/4.39           (k3_xboole_0 @ sk_B @ X0))
% 4.16/4.39           = (k3_xboole_0 @ 
% 4.16/4.39              (k2_zfmisc_1 @ sk_C @ (k2_xboole_0 @ sk_D @ sk_B)) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X1 @ X0)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['15', '16'])).
% 4.16/4.39  thf('18', plain,
% 4.16/4.39      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X38 @ X40) @ (k3_xboole_0 @ X39 @ X41))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X40 @ X41)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.16/4.39  thf('19', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ X1) @ 
% 4.16/4.39           (k3_xboole_0 @ sk_B @ X0))
% 4.16/4.39           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ X1) @ 
% 4.16/4.39              (k3_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ X0)))),
% 4.16/4.39      inference('demod', [status(thm)], ['17', '18'])).
% 4.16/4.39  thf('20', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ (k3_xboole_0 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_C) @ 
% 4.16/4.39         (k3_xboole_0 @ sk_B @ sk_D))
% 4.16/4.39         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ 
% 4.16/4.39            (k3_xboole_0 @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['8', '19'])).
% 4.16/4.39  thf(commutativity_k3_xboole_0, axiom,
% 4.16/4.39    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.16/4.39  thf('21', plain,
% 4.16/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.16/4.39  thf(t7_xboole_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.16/4.39  thf('22', plain,
% 4.16/4.39      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 4.16/4.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.16/4.39  thf(l32_xboole_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.16/4.39  thf('23', plain,
% 4.16/4.39      (![X7 : $i, X9 : $i]:
% 4.16/4.39         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 4.16/4.39      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.16/4.39  thf('24', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['22', '23'])).
% 4.16/4.39  thf(t48_xboole_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.16/4.39  thf('25', plain,
% 4.16/4.39      (![X24 : $i, X25 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 4.16/4.39           = (k3_xboole_0 @ X24 @ X25))),
% 4.16/4.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.39  thf('26', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X1 @ k1_xboole_0)
% 4.16/4.39           = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['24', '25'])).
% 4.16/4.39  thf(t3_boole, axiom,
% 4.16/4.39    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 4.16/4.39  thf('27', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 4.16/4.39      inference('cnf', [status(esa)], [t3_boole])).
% 4.16/4.39  thf('28', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('demod', [status(thm)], ['26', '27'])).
% 4.16/4.39  thf('29', plain,
% 4.16/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.16/4.39  thf('30', plain,
% 4.16/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.16/4.39  thf('31', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.16/4.39      inference('simplify', [status(thm)], ['0'])).
% 4.16/4.39  thf(t10_xboole_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 4.16/4.39  thf('32', plain,
% 4.16/4.39      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.16/4.39         (~ (r1_tarski @ X10 @ X11)
% 4.16/4.39          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.16/4.39  thf('33', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['31', '32'])).
% 4.16/4.39  thf('34', plain,
% 4.16/4.39      (![X7 : $i, X9 : $i]:
% 4.16/4.39         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 4.16/4.39      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.16/4.39  thf('35', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['33', '34'])).
% 4.16/4.39  thf('36', plain,
% 4.16/4.39      (![X24 : $i, X25 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 4.16/4.39           = (k3_xboole_0 @ X24 @ X25))),
% 4.16/4.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.39  thf('37', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 4.16/4.39           = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['35', '36'])).
% 4.16/4.39  thf('38', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 4.16/4.39      inference('cnf', [status(esa)], [t3_boole])).
% 4.16/4.39  thf('39', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('demod', [status(thm)], ['37', '38'])).
% 4.16/4.39  thf('40', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B))
% 4.16/4.39         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['20', '21', '28', '29', '30', '39'])).
% 4.16/4.39  thf('41', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf(t117_zfmisc_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.16/4.39          ( ( r1_tarski @ ( k2_zfmisc_1 @ B @ A ) @ ( k2_zfmisc_1 @ C @ A ) ) | 
% 4.16/4.39            ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ A @ C ) ) ) & 
% 4.16/4.39          ( ~( r1_tarski @ B @ C ) ) ) ))).
% 4.16/4.39  thf('42', plain,
% 4.16/4.39      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.16/4.39         (((X31) = (k1_xboole_0))
% 4.16/4.39          | (r1_tarski @ X32 @ X33)
% 4.16/4.39          | ~ (r1_tarski @ (k2_zfmisc_1 @ X32 @ X31) @ 
% 4.16/4.39               (k2_zfmisc_1 @ X33 @ X31)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 4.16/4.39  thf('43', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39             (k2_zfmisc_1 @ X0 @ sk_B))
% 4.16/4.39          | (r1_tarski @ sk_A @ X0)
% 4.16/4.39          | ((sk_B) = (k1_xboole_0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['41', '42'])).
% 4.16/4.39  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('45', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39             (k2_zfmisc_1 @ X0 @ sk_B))
% 4.16/4.39          | (r1_tarski @ sk_A @ X0))),
% 4.16/4.39      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 4.16/4.39  thf('46', plain,
% 4.16/4.39      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39           (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))
% 4.16/4.39        | (r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['40', '45'])).
% 4.16/4.39  thf('47', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((X0) = (k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('demod', [status(thm)], ['37', '38'])).
% 4.16/4.39  thf('48', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['10', '11'])).
% 4.16/4.39  thf('49', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['22', '23'])).
% 4.16/4.39  thf('50', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)) = (k1_xboole_0))),
% 4.16/4.39      inference('sup+', [status(thm)], ['48', '49'])).
% 4.16/4.39  thf('51', plain,
% 4.16/4.39      (![X24 : $i, X25 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 4.16/4.39           = (k3_xboole_0 @ X24 @ X25))),
% 4.16/4.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.39  thf('52', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ k1_xboole_0)
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39              (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['50', '51'])).
% 4.16/4.39  thf('53', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 4.16/4.39      inference('cnf', [status(esa)], [t3_boole])).
% 4.16/4.39  thf('54', plain,
% 4.16/4.39      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X38 @ X40) @ (k3_xboole_0 @ X39 @ X41))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X40 @ X41)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.16/4.39  thf('55', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ sk_C @ sk_D)
% 4.16/4.39           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ sk_A @ X0)) @ 
% 4.16/4.39              (k3_xboole_0 @ sk_D @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['52', '53', '54'])).
% 4.16/4.39  thf('56', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_C @ sk_D)
% 4.16/4.39         = (k2_zfmisc_1 @ sk_C @ (k3_xboole_0 @ sk_D @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['47', '55'])).
% 4.16/4.39  thf('57', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.16/4.39      inference('simplify', [status(thm)], ['0'])).
% 4.16/4.39  thf('58', plain, ((r1_tarski @ sk_A @ (k3_xboole_0 @ sk_C @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['46', '56', '57'])).
% 4.16/4.39  thf('59', plain,
% 4.16/4.39      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.16/4.39  thf(t22_xboole_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.16/4.39  thf('60', plain,
% 4.16/4.39      (![X18 : $i, X19 : $i]:
% 4.16/4.39         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 4.16/4.39      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.16/4.39  thf('61', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 4.16/4.39      inference('sup+', [status(thm)], ['59', '60'])).
% 4.16/4.39  thf('62', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['31', '32'])).
% 4.16/4.39  thf('63', plain,
% 4.16/4.39      (![X4 : $i, X6 : $i]:
% 4.16/4.39         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.16/4.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.39  thf('64', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.16/4.39          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['62', '63'])).
% 4.16/4.39  thf('65', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.16/4.39          | ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.16/4.39              = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['61', '64'])).
% 4.16/4.39  thf('66', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)) = (X0))),
% 4.16/4.39      inference('sup+', [status(thm)], ['59', '60'])).
% 4.16/4.39  thf('67', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         (~ (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 4.16/4.39          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('demod', [status(thm)], ['65', '66'])).
% 4.16/4.39  thf('68', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 4.16/4.39      inference('sup-', [status(thm)], ['58', '67'])).
% 4.16/4.39  thf('69', plain,
% 4.16/4.39      (![X18 : $i, X19 : $i]:
% 4.16/4.39         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 4.16/4.39      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.16/4.39  thf('70', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['31', '32'])).
% 4.16/4.39  thf('71', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 4.16/4.39      inference('sup+', [status(thm)], ['69', '70'])).
% 4.16/4.39  thf('72', plain,
% 4.16/4.39      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.16/4.39         (~ (r1_tarski @ X10 @ X11)
% 4.16/4.39          | (r1_tarski @ X10 @ (k2_xboole_0 @ X12 @ X11)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t10_xboole_1])).
% 4.16/4.39  thf('73', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.39         (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['71', '72'])).
% 4.16/4.39  thf('74', plain,
% 4.16/4.39      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ sk_C))),
% 4.16/4.39      inference('sup+', [status(thm)], ['68', '73'])).
% 4.16/4.39  thf('75', plain,
% 4.16/4.39      (![X4 : $i, X6 : $i]:
% 4.16/4.39         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.16/4.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.39  thf('76', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ sk_C) @ sk_A)
% 4.16/4.39          | ((k2_xboole_0 @ X0 @ sk_C) = (sk_A)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['74', '75'])).
% 4.16/4.39  thf('77', plain,
% 4.16/4.39      ((~ (r1_tarski @ sk_C @ sk_A) | ((k2_xboole_0 @ sk_C @ sk_C) = (sk_A)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['3', '76'])).
% 4.16/4.39  thf('78', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['1', '2'])).
% 4.16/4.39  thf('79', plain, ((~ (r1_tarski @ sk_C @ sk_A) | ((sk_C) = (sk_A)))),
% 4.16/4.39      inference('demod', [status(thm)], ['77', '78'])).
% 4.16/4.39  thf('80', plain, ((((sk_A) != (sk_C)) | ((sk_B) != (sk_D)))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('81', plain, ((((sk_A) != (sk_C))) <= (~ (((sk_A) = (sk_C))))),
% 4.16/4.39      inference('split', [status(esa)], ['80'])).
% 4.16/4.39  thf('82', plain,
% 4.16/4.39      (![X34 : $i, X35 : $i, X36 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k2_xboole_0 @ X34 @ X36) @ X35)
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ X34 @ X35) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X36 @ X35)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.16/4.39  thf('83', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('84', plain,
% 4.16/4.39      (![X34 : $i, X36 : $i, X37 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ X37 @ (k2_xboole_0 @ X34 @ X36))
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ X37 @ X34) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X37 @ X36)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 4.16/4.39  thf('85', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39              (k2_zfmisc_1 @ sk_A @ X0)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['83', '84'])).
% 4.16/4.39  thf('86', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_B @ sk_D))
% 4.16/4.39         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 4.16/4.39      inference('sup+', [status(thm)], ['82', '85'])).
% 4.16/4.39  thf('87', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.16/4.39  thf('88', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ (k2_xboole_0 @ sk_D @ sk_B))
% 4.16/4.39         = (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 4.16/4.39      inference('demod', [status(thm)], ['86', '87'])).
% 4.16/4.39  thf('89', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('90', plain,
% 4.16/4.39      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.16/4.39         (((X31) = (k1_xboole_0))
% 4.16/4.39          | (r1_tarski @ X32 @ X33)
% 4.16/4.39          | ~ (r1_tarski @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 4.16/4.39               (k2_zfmisc_1 @ X31 @ X33)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 4.16/4.39  thf('91', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39          | (r1_tarski @ X0 @ sk_B)
% 4.16/4.39          | ((sk_A) = (k1_xboole_0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['89', '90'])).
% 4.16/4.39  thf('92', plain, (((sk_A) != (k1_xboole_0))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('93', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39          | (r1_tarski @ X0 @ sk_B))),
% 4.16/4.39      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 4.16/4.39  thf('94', plain,
% 4.16/4.39      ((~ (r1_tarski @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_A) @ sk_D) @ 
% 4.16/4.39           (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39        | (r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B))),
% 4.16/4.39      inference('sup-', [status(thm)], ['88', '93'])).
% 4.16/4.39  thf('95', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 4.16/4.39      inference('sup-', [status(thm)], ['58', '67'])).
% 4.16/4.39  thf('96', plain,
% 4.16/4.39      (![X18 : $i, X19 : $i]:
% 4.16/4.39         ((k2_xboole_0 @ X18 @ (k3_xboole_0 @ X18 @ X19)) = (X18))),
% 4.16/4.39      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.16/4.39  thf('97', plain, (((k2_xboole_0 @ sk_C @ sk_A) = (sk_C))),
% 4.16/4.39      inference('sup+', [status(thm)], ['95', '96'])).
% 4.16/4.39  thf('98', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.16/4.39      inference('simplify', [status(thm)], ['0'])).
% 4.16/4.39  thf('99', plain, ((r1_tarski @ (k2_xboole_0 @ sk_D @ sk_B) @ sk_B)),
% 4.16/4.39      inference('demod', [status(thm)], ['94', '97', '98'])).
% 4.16/4.39  thf('100', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 4.16/4.39          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['62', '63'])).
% 4.16/4.39  thf('101', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 4.16/4.39      inference('sup-', [status(thm)], ['99', '100'])).
% 4.16/4.39  thf('102', plain,
% 4.16/4.39      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 4.16/4.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.16/4.39  thf('103', plain,
% 4.16/4.39      (![X4 : $i, X6 : $i]:
% 4.16/4.39         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 4.16/4.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.39  thf('104', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 4.16/4.39          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['102', '103'])).
% 4.16/4.39  thf('105', plain,
% 4.16/4.39      ((~ (r1_tarski @ sk_B @ sk_D) | ((k2_xboole_0 @ sk_D @ sk_B) = (sk_D)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['101', '104'])).
% 4.16/4.39  thf('106', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 4.16/4.39      inference('sup-', [status(thm)], ['99', '100'])).
% 4.16/4.39  thf('107', plain, ((~ (r1_tarski @ sk_B @ sk_D) | ((sk_B) = (sk_D)))),
% 4.16/4.39      inference('demod', [status(thm)], ['105', '106'])).
% 4.16/4.39  thf('108', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['1', '2'])).
% 4.16/4.39  thf('109', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 4.16/4.39      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 4.16/4.39  thf('110', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B)
% 4.16/4.39           = (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X0 @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['10', '11'])).
% 4.16/4.39  thf('111', plain,
% 4.16/4.39      (![X26 : $i, X27 : $i]: (r1_tarski @ X26 @ (k2_xboole_0 @ X26 @ X27))),
% 4.16/4.39      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.16/4.39  thf('112', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['110', '111'])).
% 4.16/4.39  thf('113', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39          (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['109', '112'])).
% 4.16/4.39  thf('114', plain,
% 4.16/4.39      (![X7 : $i, X9 : $i]:
% 4.16/4.39         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 4.16/4.39      inference('cnf', [status(esa)], [l32_xboole_1])).
% 4.16/4.39  thf('115', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39           (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)) = (k1_xboole_0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['113', '114'])).
% 4.16/4.39  thf('116', plain,
% 4.16/4.39      (![X24 : $i, X25 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ X24 @ (k4_xboole_0 @ X24 @ X25))
% 4.16/4.39           = (k3_xboole_0 @ X24 @ X25))),
% 4.16/4.39      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.16/4.39  thf('117', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k4_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ k1_xboole_0)
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39              (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_A) @ sk_B)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['115', '116'])).
% 4.16/4.39  thf('118', plain, (![X21 : $i]: ((k4_xboole_0 @ X21 @ k1_xboole_0) = (X21))),
% 4.16/4.39      inference('cnf', [status(esa)], [t3_boole])).
% 4.16/4.39  thf('119', plain,
% 4.16/4.39      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ (k3_xboole_0 @ X38 @ X40) @ (k3_xboole_0 @ X39 @ X41))
% 4.16/4.39           = (k3_xboole_0 @ (k2_zfmisc_1 @ X38 @ X39) @ 
% 4.16/4.39              (k2_zfmisc_1 @ X40 @ X41)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 4.16/4.39  thf('120', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ sk_C @ sk_D)
% 4.16/4.39           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A)) @ 
% 4.16/4.39              (k3_xboole_0 @ sk_D @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['117', '118', '119'])).
% 4.16/4.39  thf('121', plain, (((k2_xboole_0 @ sk_D @ sk_B) = (sk_B))),
% 4.16/4.39      inference('sup-', [status(thm)], ['99', '100'])).
% 4.16/4.39  thf('122', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]:
% 4.16/4.39         ((X1) = (k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 4.16/4.39      inference('demod', [status(thm)], ['26', '27'])).
% 4.16/4.39  thf('123', plain, (((sk_D) = (k3_xboole_0 @ sk_D @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['121', '122'])).
% 4.16/4.39  thf('124', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_zfmisc_1 @ sk_C @ sk_D)
% 4.16/4.39           = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ (k2_xboole_0 @ X0 @ sk_A)) @ 
% 4.16/4.39              sk_D))),
% 4.16/4.39      inference('demod', [status(thm)], ['120', '123'])).
% 4.16/4.39  thf('125', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_C @ sk_D)
% 4.16/4.39         = (k2_zfmisc_1 @ (k3_xboole_0 @ sk_C @ sk_A) @ sk_D))),
% 4.16/4.39      inference('sup+', [status(thm)], ['108', '124'])).
% 4.16/4.39  thf('126', plain, (((sk_A) = (k3_xboole_0 @ sk_C @ sk_A))),
% 4.16/4.39      inference('sup-', [status(thm)], ['58', '67'])).
% 4.16/4.39  thf('127', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_C @ sk_D) = (k2_zfmisc_1 @ sk_A @ sk_D))),
% 4.16/4.39      inference('demod', [status(thm)], ['125', '126'])).
% 4.16/4.39  thf('128', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('129', plain,
% 4.16/4.39      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.16/4.39         (((X31) = (k1_xboole_0))
% 4.16/4.39          | (r1_tarski @ X32 @ X33)
% 4.16/4.39          | ~ (r1_tarski @ (k2_zfmisc_1 @ X31 @ X32) @ 
% 4.16/4.39               (k2_zfmisc_1 @ X31 @ X33)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 4.16/4.39  thf('130', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_A @ X0))
% 4.16/4.39          | (r1_tarski @ sk_B @ X0)
% 4.16/4.39          | ((sk_A) = (k1_xboole_0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['128', '129'])).
% 4.16/4.39  thf('131', plain, (((sk_A) != (k1_xboole_0))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('132', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_A @ X0))
% 4.16/4.39          | (r1_tarski @ sk_B @ X0))),
% 4.16/4.39      inference('simplify_reflect-', [status(thm)], ['130', '131'])).
% 4.16/4.39  thf('133', plain,
% 4.16/4.39      ((~ (r1_tarski @ (k2_zfmisc_1 @ sk_C @ sk_D) @ 
% 4.16/4.39           (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39        | (r1_tarski @ sk_B @ sk_D))),
% 4.16/4.39      inference('sup-', [status(thm)], ['127', '132'])).
% 4.16/4.39  thf('134', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.16/4.39      inference('simplify', [status(thm)], ['0'])).
% 4.16/4.39  thf('135', plain, ((r1_tarski @ sk_B @ sk_D)),
% 4.16/4.39      inference('demod', [status(thm)], ['133', '134'])).
% 4.16/4.39  thf('136', plain, (((sk_B) = (sk_D))),
% 4.16/4.39      inference('demod', [status(thm)], ['107', '135'])).
% 4.16/4.39  thf('137', plain, ((((sk_B) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 4.16/4.39      inference('split', [status(esa)], ['80'])).
% 4.16/4.39  thf('138', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B) = (sk_D))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['136', '137'])).
% 4.16/4.39  thf('139', plain, ((((sk_B) = (sk_D)))),
% 4.16/4.39      inference('simplify', [status(thm)], ['138'])).
% 4.16/4.39  thf('140', plain, (~ (((sk_A) = (sk_C))) | ~ (((sk_B) = (sk_D)))),
% 4.16/4.39      inference('split', [status(esa)], ['80'])).
% 4.16/4.39  thf('141', plain, (~ (((sk_A) = (sk_C)))),
% 4.16/4.39      inference('sat_resolution*', [status(thm)], ['139', '140'])).
% 4.16/4.39  thf('142', plain, (((sk_A) != (sk_C))),
% 4.16/4.39      inference('simpl_trail', [status(thm)], ['81', '141'])).
% 4.16/4.39  thf('143', plain, (~ (r1_tarski @ sk_C @ sk_A)),
% 4.16/4.39      inference('simplify_reflect-', [status(thm)], ['79', '142'])).
% 4.16/4.39  thf('144', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 4.16/4.39      inference('simplify', [status(thm)], ['0'])).
% 4.16/4.39  thf('145', plain,
% 4.16/4.39      (((k2_zfmisc_1 @ sk_A @ sk_B) = (k2_zfmisc_1 @ sk_C @ sk_D))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('146', plain,
% 4.16/4.39      (![X31 : $i, X32 : $i, X33 : $i]:
% 4.16/4.39         (((X31) = (k1_xboole_0))
% 4.16/4.39          | (r1_tarski @ X32 @ X33)
% 4.16/4.39          | ~ (r1_tarski @ (k2_zfmisc_1 @ X32 @ X31) @ 
% 4.16/4.39               (k2_zfmisc_1 @ X33 @ X31)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t117_zfmisc_1])).
% 4.16/4.39  thf('147', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39          | (r1_tarski @ X0 @ sk_A)
% 4.16/4.39          | ((sk_B) = (k1_xboole_0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['145', '146'])).
% 4.16/4.39  thf('148', plain, (((sk_B) != (k1_xboole_0))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('149', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39          | (r1_tarski @ X0 @ sk_A))),
% 4.16/4.39      inference('simplify_reflect-', [status(thm)], ['147', '148'])).
% 4.16/4.39  thf('150', plain, (((sk_B) = (sk_D))),
% 4.16/4.39      inference('demod', [status(thm)], ['107', '135'])).
% 4.16/4.39  thf('151', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_D) @ 
% 4.16/4.39             (k2_zfmisc_1 @ sk_C @ sk_D))
% 4.16/4.39          | (r1_tarski @ X0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['149', '150'])).
% 4.16/4.39  thf('152', plain, ((r1_tarski @ sk_C @ sk_A)),
% 4.16/4.39      inference('sup-', [status(thm)], ['144', '151'])).
% 4.16/4.39  thf('153', plain, ($false), inference('demod', [status(thm)], ['143', '152'])).
% 4.16/4.39  
% 4.16/4.39  % SZS output end Refutation
% 4.16/4.39  
% 4.16/4.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
