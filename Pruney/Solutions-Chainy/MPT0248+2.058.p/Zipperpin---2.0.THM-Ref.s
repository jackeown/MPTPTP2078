%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QlowkEWTje

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:26 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  189 (2509 expanded)
%              Number of leaves         :   34 ( 752 expanded)
%              Depth                    :   26
%              Number of atoms          : 1127 (24245 expanded)
%              Number of equality atoms :  175 (4186 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X64 ) @ X65 )
      | ( r2_hidden @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('8',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
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

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('19',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k3_xboole_0 @ X67 @ ( k1_tarski @ X66 ) )
        = ( k1_tarski @ X66 ) )
      | ~ ( r2_hidden @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('22',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('24',plain,
    ( ( ( sk_B_1 != sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('27',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X34: $i,X35: $i] :
      ( r1_tarski @ X34 @ ( k2_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('31',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('32',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( k2_xboole_0 @ sk_B_1 @ X0 )
        = X0 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X0 @ X1 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('44',plain,(
    ! [X36: $i] :
      ( ( k2_tarski @ X36 @ X36 )
      = ( k1_tarski @ X36 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('45',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('47',plain,(
    ! [X29: $i] :
      ( ( k3_xboole_0 @ X29 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('48',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ X18 )
      = ( k5_xboole_0 @ X17 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('50',plain,(
    ! [X33: $i] :
      ( ( k5_xboole_0 @ X33 @ k1_xboole_0 )
      = X33 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('55',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,
    ( ( ( k1_tarski @ ( k3_tarski @ sk_C_1 ) )
      = sk_C_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','55'])).

thf('57',plain,
    ( ( ( k3_tarski @ sk_C_1 )
      = sk_A )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('58',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
   <= ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('61',plain,
    ( ( sk_B_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_C_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( sk_C_1
     != ( k1_tarski @ sk_A ) )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['61'])).

thf('63',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('64',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 != X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['60','62','68'])).

thf('70',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','69'])).

thf('71',plain,
    ( ( sk_C_1
     != ( k1_tarski @ ( k3_tarski @ sk_C_1 ) ) )
   <= ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','70'])).

thf('72',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['56','71'])).

thf('73',plain,
    ( ( sk_C_1 != k1_xboole_0 )
    | ( sk_B_1
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('74',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['4','74'])).

thf('76',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['46','53'])).

thf('79',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('81',plain,
    ( ( ( k3_tarski @ sk_B_1 )
      = sk_A )
    | ( ( k1_tarski @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','69'])).

thf('83',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('86',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('87',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('88',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_xboole_0 @ sk_B_1 @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('91',plain,
    ( ( sk_B_1
      = ( k1_tarski @ sk_A ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('93',plain,
    ( ( sk_B_1
      = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('95',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','69'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','96'])).

thf('98',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['84','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('100',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('101',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r1_tarski @ X22 @ ( k2_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    r1_tarski @ sk_C_1 @ sk_B_1 ),
    inference('sup+',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('106',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('108',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','96'])).

thf('110',plain,(
    ! [X64: $i,X65: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X64 ) @ X65 )
      | ( r2_hidden @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X66: $i,X67: $i] :
      ( ( ( k3_xboole_0 @ X67 @ ( k1_tarski @ X66 ) )
        = ( k1_tarski @ X66 ) )
      | ~ ( r2_hidden @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
        = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','96'])).

thf('115',plain,
    ( sk_B_1
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['93','96'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B_1 @ X0 )
      | ( ( k3_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 ) ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B_1 @ X0 )
        = sk_B_1 )
      | ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( sk_C_1 = sk_B_1 )
    | ( r1_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['108','118'])).

thf('120',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('121',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('122',plain,(
    ! [X14: $i,X16: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X16 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('123',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X30: $i,X31: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X30 @ X31 ) @ X30 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('125',plain,(
    r1_tarski @ k1_xboole_0 @ sk_B_1 ),
    inference('sup+',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_xboole_0 @ X26 @ X25 )
        = X25 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('127',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_B_1 )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( ( k2_xboole_0 @ X0 @ sk_B_1 )
        = sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['120','127'])).

thf('129',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('132',plain,
    ( ( k3_tarski @ ( k1_tarski @ k1_xboole_0 ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k3_tarski @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['129','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( sk_C_1 != k1_xboole_0 )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('137',plain,
    ( ! [X0: $i] :
        ( ( sk_C_1
         != ( k2_xboole_0 @ X0 @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( sk_C_1 != sk_B_1 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['128','137'])).

thf('139',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( sk_C_1 != sk_B_1 ) )
   <= ( sk_C_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('141',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 != sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['139','140'])).

thf('142',plain,
    ( ( ( k1_tarski @ sk_A )
      = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('143',plain,(
    sk_C_1
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['59','69'])).

thf('144',plain,
    ( ( sk_C_1 != sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    sk_C_1 != sk_B_1 ),
    inference(clc,[status(thm)],['141','144'])).

thf('146',plain,(
    r1_xboole_0 @ sk_B_1 @ sk_C_1 ),
    inference('simplify_reflect-',[status(thm)],['119','145'])).

thf('147',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('148',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['146','149'])).

thf('151',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_1 )
    = sk_C_1 ),
    inference(demod,[status(thm)],['106','107'])).

thf('152',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['150','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['75','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QlowkEWTje
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:56:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.26/1.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.26/1.46  % Solved by: fo/fo7.sh
% 1.26/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.26/1.46  % done 2947 iterations in 1.002s
% 1.26/1.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.26/1.46  % SZS output start Refutation
% 1.26/1.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.26/1.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.26/1.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.26/1.46  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.26/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.26/1.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.26/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.26/1.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.26/1.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.26/1.46  thf(sk_B_type, type, sk_B: $i > $i).
% 1.26/1.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.26/1.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.26/1.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.26/1.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.26/1.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.26/1.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.26/1.46  thf(l13_xboole_0, axiom,
% 1.26/1.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.26/1.46  thf('0', plain,
% 1.26/1.46      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.26/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.26/1.46  thf(t43_zfmisc_1, conjecture,
% 1.26/1.46    (![A:$i,B:$i,C:$i]:
% 1.26/1.46     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.26/1.46          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.26/1.46          ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.26/1.46          ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 1.26/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.26/1.46    (~( ![A:$i,B:$i,C:$i]:
% 1.26/1.46        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.26/1.46             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.26/1.46             ( ~( ( ( B ) = ( k1_xboole_0 ) ) & ( ( C ) = ( k1_tarski @ A ) ) ) ) & 
% 1.26/1.46             ( ~( ( ( B ) = ( k1_tarski @ A ) ) & ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 1.26/1.46    inference('cnf.neg', [status(esa)], [t43_zfmisc_1])).
% 1.26/1.46  thf('1', plain,
% 1.26/1.46      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_xboole_0)))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf('2', plain,
% 1.26/1.46      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('split', [status(esa)], ['1'])).
% 1.26/1.46  thf('3', plain,
% 1.26/1.46      ((![X0 : $i]: (((sk_C_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.26/1.46         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['0', '2'])).
% 1.26/1.46  thf('4', plain,
% 1.26/1.46      ((~ (v1_xboole_0 @ sk_C_1)) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('simplify', [status(thm)], ['3'])).
% 1.26/1.46  thf('5', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf(d1_xboole_0, axiom,
% 1.26/1.46    (![A:$i]:
% 1.26/1.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.26/1.46  thf('6', plain,
% 1.26/1.46      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.26/1.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.26/1.46  thf(l27_zfmisc_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.26/1.46  thf('7', plain,
% 1.26/1.46      (![X64 : $i, X65 : $i]:
% 1.26/1.46         ((r1_xboole_0 @ (k1_tarski @ X64) @ X65) | (r2_hidden @ X64 @ X65))),
% 1.26/1.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.26/1.46  thf('8', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf(t7_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.26/1.46  thf('9', plain,
% 1.26/1.46      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 1.26/1.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.26/1.46  thf('10', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.26/1.46      inference('sup+', [status(thm)], ['8', '9'])).
% 1.26/1.46  thf(t28_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.26/1.46  thf('11', plain,
% 1.26/1.46      (![X27 : $i, X28 : $i]:
% 1.26/1.46         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 1.26/1.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.26/1.46  thf('12', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['10', '11'])).
% 1.26/1.46  thf(commutativity_k3_xboole_0, axiom,
% 1.26/1.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.26/1.46  thf('13', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.26/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.26/1.46  thf(t4_xboole_0, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.26/1.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.26/1.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.26/1.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.26/1.46  thf('14', plain,
% 1.26/1.46      (![X10 : $i, X12 : $i, X13 : $i]:
% 1.26/1.46         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 1.26/1.46          | ~ (r1_xboole_0 @ X10 @ X13))),
% 1.26/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.26/1.46  thf('15', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.26/1.46         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 1.26/1.46          | ~ (r1_xboole_0 @ X0 @ X1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['13', '14'])).
% 1.26/1.46  thf('16', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         (~ (r2_hidden @ X0 @ sk_B_1)
% 1.26/1.46          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['12', '15'])).
% 1.26/1.46  thf('17', plain,
% 1.26/1.46      (![X0 : $i]: ((r2_hidden @ sk_A @ sk_B_1) | ~ (r2_hidden @ X0 @ sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['7', '16'])).
% 1.26/1.46  thf('18', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_A @ sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['6', '17'])).
% 1.26/1.46  thf(l31_zfmisc_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( r2_hidden @ A @ B ) =>
% 1.26/1.46       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 1.26/1.46  thf('19', plain,
% 1.26/1.46      (![X66 : $i, X67 : $i]:
% 1.26/1.46         (((k3_xboole_0 @ X67 @ (k1_tarski @ X66)) = (k1_tarski @ X66))
% 1.26/1.46          | ~ (r2_hidden @ X66 @ X67))),
% 1.26/1.46      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.26/1.46  thf('20', plain,
% 1.26/1.46      (((v1_xboole_0 @ sk_B_1)
% 1.26/1.46        | ((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('sup-', [status(thm)], ['18', '19'])).
% 1.26/1.46  thf('21', plain, (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['10', '11'])).
% 1.26/1.46  thf('22', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['20', '21'])).
% 1.26/1.46  thf('23', plain,
% 1.26/1.46      ((((sk_B_1) != (k1_tarski @ sk_A)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('split', [status(esa)], ['1'])).
% 1.26/1.46  thf('24', plain,
% 1.26/1.46      (((((sk_B_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['22', '23'])).
% 1.26/1.46  thf('25', plain,
% 1.26/1.46      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('simplify', [status(thm)], ['24'])).
% 1.26/1.46  thf('26', plain,
% 1.26/1.46      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.26/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.26/1.46  thf('27', plain,
% 1.26/1.46      ((((sk_B_1) = (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['25', '26'])).
% 1.26/1.46  thf('28', plain,
% 1.26/1.46      (![X34 : $i, X35 : $i]: (r1_tarski @ X34 @ (k2_xboole_0 @ X34 @ X35))),
% 1.26/1.46      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.26/1.46  thf(l32_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.26/1.46  thf('29', plain,
% 1.26/1.46      (![X14 : $i, X16 : $i]:
% 1.26/1.46         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 1.26/1.46          | ~ (r1_tarski @ X14 @ X16))),
% 1.26/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.26/1.46  thf('30', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]:
% 1.26/1.46         ((k4_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 1.26/1.46      inference('sup-', [status(thm)], ['28', '29'])).
% 1.26/1.46  thf(t36_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.26/1.46  thf('31', plain,
% 1.26/1.46      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 1.26/1.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.26/1.46  thf(t12_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.26/1.46  thf('32', plain,
% 1.26/1.46      (![X25 : $i, X26 : $i]:
% 1.26/1.46         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 1.26/1.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.26/1.46  thf('33', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]:
% 1.26/1.46         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.26/1.46      inference('sup-', [status(thm)], ['31', '32'])).
% 1.26/1.46  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['30', '33'])).
% 1.26/1.46  thf('35', plain,
% 1.26/1.46      ((![X0 : $i]: ((k2_xboole_0 @ sk_B_1 @ X0) = (X0)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup+', [status(thm)], ['27', '34'])).
% 1.26/1.46  thf('36', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup+', [status(thm)], ['5', '35'])).
% 1.26/1.46  thf('37', plain,
% 1.26/1.46      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('simplify', [status(thm)], ['24'])).
% 1.26/1.46  thf('38', plain,
% 1.26/1.46      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.26/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.26/1.46  thf('39', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['30', '33'])).
% 1.26/1.46  thf('40', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]:
% 1.26/1.46         (((k2_xboole_0 @ X0 @ X1) = (X1)) | ~ (v1_xboole_0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['38', '39'])).
% 1.26/1.46  thf('41', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf('42', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['40', '41'])).
% 1.26/1.46  thf('43', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_C_1)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['37', '42'])).
% 1.26/1.46  thf(t69_enumset1, axiom,
% 1.26/1.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.26/1.46  thf('44', plain,
% 1.26/1.46      (![X36 : $i]: ((k2_tarski @ X36 @ X36) = (k1_tarski @ X36))),
% 1.26/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.26/1.46  thf(l51_zfmisc_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.26/1.46  thf('45', plain,
% 1.26/1.46      (![X68 : $i, X69 : $i]:
% 1.26/1.46         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 1.26/1.46      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.26/1.46  thf('46', plain,
% 1.26/1.46      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['44', '45'])).
% 1.26/1.46  thf(t2_boole, axiom,
% 1.26/1.46    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.26/1.46  thf('47', plain,
% 1.26/1.46      (![X29 : $i]: ((k3_xboole_0 @ X29 @ k1_xboole_0) = (k1_xboole_0))),
% 1.26/1.46      inference('cnf', [status(esa)], [t2_boole])).
% 1.26/1.46  thf(t100_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i]:
% 1.26/1.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.26/1.46  thf('48', plain,
% 1.26/1.46      (![X17 : $i, X18 : $i]:
% 1.26/1.46         ((k4_xboole_0 @ X17 @ X18)
% 1.26/1.46           = (k5_xboole_0 @ X17 @ (k3_xboole_0 @ X17 @ X18)))),
% 1.26/1.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.26/1.46  thf('49', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['47', '48'])).
% 1.26/1.46  thf(t5_boole, axiom,
% 1.26/1.46    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.26/1.46  thf('50', plain, (![X33 : $i]: ((k5_xboole_0 @ X33 @ k1_xboole_0) = (X33))),
% 1.26/1.46      inference('cnf', [status(esa)], [t5_boole])).
% 1.26/1.46  thf('51', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['49', '50'])).
% 1.26/1.46  thf('52', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]:
% 1.26/1.46         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 1.26/1.46      inference('sup-', [status(thm)], ['31', '32'])).
% 1.26/1.46  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['51', '52'])).
% 1.26/1.46  thf('54', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.26/1.46      inference('demod', [status(thm)], ['46', '53'])).
% 1.26/1.46  thf('55', plain,
% 1.26/1.46      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup+', [status(thm)], ['43', '54'])).
% 1.26/1.46  thf('56', plain,
% 1.26/1.46      ((((k1_tarski @ (k3_tarski @ sk_C_1)) = (sk_C_1)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('demod', [status(thm)], ['36', '55'])).
% 1.26/1.46  thf('57', plain,
% 1.26/1.46      ((((k3_tarski @ sk_C_1) = (sk_A)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup+', [status(thm)], ['43', '54'])).
% 1.26/1.46  thf('58', plain,
% 1.26/1.46      ((((sk_B_1) != (k1_xboole_0)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf('59', plain,
% 1.26/1.46      ((((sk_C_1) != (k1_tarski @ sk_A)))
% 1.26/1.46         <= (~ (((sk_C_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('split', [status(esa)], ['58'])).
% 1.26/1.46  thf('60', plain,
% 1.26/1.46      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 1.26/1.46      inference('split', [status(esa)], ['58'])).
% 1.26/1.46  thf('61', plain,
% 1.26/1.46      ((((sk_B_1) != (k1_tarski @ sk_A)) | ((sk_C_1) != (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf('62', plain,
% 1.26/1.46      (~ (((sk_C_1) = (k1_tarski @ sk_A))) | 
% 1.26/1.46       ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('split', [status(esa)], ['61'])).
% 1.26/1.46  thf('63', plain,
% 1.26/1.46      (((v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('simplify', [status(thm)], ['24'])).
% 1.26/1.46  thf('64', plain,
% 1.26/1.46      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.26/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.26/1.46  thf('65', plain,
% 1.26/1.46      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('split', [status(esa)], ['58'])).
% 1.26/1.46  thf('66', plain,
% 1.26/1.46      ((![X0 : $i]: (((sk_B_1) != (X0)) | ~ (v1_xboole_0 @ X0)))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['64', '65'])).
% 1.26/1.46  thf('67', plain,
% 1.26/1.46      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('simplify', [status(thm)], ['66'])).
% 1.26/1.46  thf('68', plain,
% 1.26/1.46      ((((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('sup-', [status(thm)], ['63', '67'])).
% 1.26/1.46  thf('69', plain, (~ (((sk_C_1) = (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('sat_resolution*', [status(thm)], ['60', '62', '68'])).
% 1.26/1.46  thf('70', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.26/1.46      inference('simpl_trail', [status(thm)], ['59', '69'])).
% 1.26/1.46  thf('71', plain,
% 1.26/1.46      ((((sk_C_1) != (k1_tarski @ (k3_tarski @ sk_C_1))))
% 1.26/1.46         <= (~ (((sk_B_1) = (k1_tarski @ sk_A))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['57', '70'])).
% 1.26/1.46  thf('72', plain, ((((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('simplify_reflect-', [status(thm)], ['56', '71'])).
% 1.26/1.46  thf('73', plain,
% 1.26/1.46      (~ (((sk_C_1) = (k1_xboole_0))) | ~ (((sk_B_1) = (k1_tarski @ sk_A)))),
% 1.26/1.46      inference('split', [status(esa)], ['1'])).
% 1.26/1.46  thf('74', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.26/1.46      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 1.26/1.46  thf('75', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.26/1.46      inference('simpl_trail', [status(thm)], ['4', '74'])).
% 1.26/1.46  thf('76', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.26/1.46  thf('77', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['20', '21'])).
% 1.26/1.46  thf('78', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.26/1.46      inference('demod', [status(thm)], ['46', '53'])).
% 1.26/1.46  thf('79', plain,
% 1.26/1.46      ((((k3_tarski @ sk_B_1) = (sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['77', '78'])).
% 1.26/1.46  thf('80', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['40', '41'])).
% 1.26/1.46  thf('81', plain,
% 1.26/1.46      ((((k3_tarski @ sk_B_1) = (sk_A)) | ((k1_tarski @ sk_A) = (sk_C_1)))),
% 1.26/1.46      inference('sup-', [status(thm)], ['79', '80'])).
% 1.26/1.46  thf('82', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.26/1.46      inference('simpl_trail', [status(thm)], ['59', '69'])).
% 1.26/1.46  thf('83', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.26/1.46      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.26/1.46  thf('84', plain,
% 1.26/1.46      (((k1_tarski @ (k3_tarski @ sk_B_1)) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('demod', [status(thm)], ['76', '83'])).
% 1.26/1.46  thf('85', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['20', '21'])).
% 1.26/1.46  thf('86', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.26/1.46      inference('sup+', [status(thm)], ['8', '9'])).
% 1.26/1.46  thf('87', plain,
% 1.26/1.46      (![X25 : $i, X26 : $i]:
% 1.26/1.46         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 1.26/1.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.26/1.46  thf('88', plain,
% 1.26/1.46      (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.26/1.46      inference('sup-', [status(thm)], ['86', '87'])).
% 1.26/1.46  thf('89', plain,
% 1.26/1.46      ((((k2_xboole_0 @ sk_B_1 @ sk_B_1) = (k1_tarski @ sk_A))
% 1.26/1.46        | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['85', '88'])).
% 1.26/1.46  thf('90', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['51', '52'])).
% 1.26/1.46  thf('91', plain,
% 1.26/1.46      ((((sk_B_1) = (k1_tarski @ sk_A)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('demod', [status(thm)], ['89', '90'])).
% 1.26/1.46  thf('92', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.26/1.46      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 1.26/1.46  thf('93', plain,
% 1.26/1.46      ((((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))
% 1.26/1.46        | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('demod', [status(thm)], ['91', '92'])).
% 1.26/1.46  thf('94', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['40', '41'])).
% 1.26/1.46  thf('95', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.26/1.46      inference('simpl_trail', [status(thm)], ['59', '69'])).
% 1.26/1.46  thf('96', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.26/1.46      inference('simplify_reflect-', [status(thm)], ['94', '95'])).
% 1.26/1.46  thf('97', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 1.26/1.46      inference('clc', [status(thm)], ['93', '96'])).
% 1.26/1.46  thf('98', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('demod', [status(thm)], ['84', '97'])).
% 1.26/1.46  thf('99', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['49', '50'])).
% 1.26/1.46  thf('100', plain,
% 1.26/1.46      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 1.26/1.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.26/1.46  thf('101', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.26/1.46      inference('sup+', [status(thm)], ['99', '100'])).
% 1.26/1.46  thf(t10_xboole_1, axiom,
% 1.26/1.46    (![A:$i,B:$i,C:$i]:
% 1.26/1.46     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.26/1.46  thf('102', plain,
% 1.26/1.46      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.26/1.46         (~ (r1_tarski @ X22 @ X23)
% 1.26/1.46          | (r1_tarski @ X22 @ (k2_xboole_0 @ X24 @ X23)))),
% 1.26/1.46      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.26/1.46  thf('103', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.26/1.46      inference('sup-', [status(thm)], ['101', '102'])).
% 1.26/1.46  thf('104', plain, ((r1_tarski @ sk_C_1 @ sk_B_1)),
% 1.26/1.46      inference('sup+', [status(thm)], ['98', '103'])).
% 1.26/1.46  thf('105', plain,
% 1.26/1.46      (![X27 : $i, X28 : $i]:
% 1.26/1.46         (((k3_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_tarski @ X27 @ X28))),
% 1.26/1.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.26/1.46  thf('106', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B_1) = (sk_C_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['104', '105'])).
% 1.26/1.46  thf('107', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.26/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.26/1.46  thf('108', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.26/1.46      inference('demod', [status(thm)], ['106', '107'])).
% 1.26/1.46  thf('109', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 1.26/1.46      inference('clc', [status(thm)], ['93', '96'])).
% 1.26/1.46  thf('110', plain,
% 1.26/1.46      (![X64 : $i, X65 : $i]:
% 1.26/1.46         ((r1_xboole_0 @ (k1_tarski @ X64) @ X65) | (r2_hidden @ X64 @ X65))),
% 1.26/1.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.26/1.46  thf('111', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         ((r1_xboole_0 @ sk_B_1 @ X0) | (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['109', '110'])).
% 1.26/1.46  thf('112', plain,
% 1.26/1.46      (![X66 : $i, X67 : $i]:
% 1.26/1.46         (((k3_xboole_0 @ X67 @ (k1_tarski @ X66)) = (k1_tarski @ X66))
% 1.26/1.46          | ~ (r2_hidden @ X66 @ X67))),
% 1.26/1.46      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.26/1.46  thf('113', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         ((r1_xboole_0 @ sk_B_1 @ X0)
% 1.26/1.46          | ((k3_xboole_0 @ X0 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 1.26/1.46              = (k1_tarski @ (k3_tarski @ sk_B_1))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['111', '112'])).
% 1.26/1.46  thf('114', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 1.26/1.46      inference('clc', [status(thm)], ['93', '96'])).
% 1.26/1.46  thf('115', plain, (((sk_B_1) = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 1.26/1.46      inference('clc', [status(thm)], ['93', '96'])).
% 1.26/1.46  thf('116', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         ((r1_xboole_0 @ sk_B_1 @ X0)
% 1.26/1.46          | ((k3_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)))),
% 1.26/1.46      inference('demod', [status(thm)], ['113', '114', '115'])).
% 1.26/1.46  thf('117', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.26/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.26/1.46  thf('118', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         (((k3_xboole_0 @ sk_B_1 @ X0) = (sk_B_1))
% 1.26/1.46          | (r1_xboole_0 @ sk_B_1 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['116', '117'])).
% 1.26/1.46  thf('119', plain,
% 1.26/1.46      ((((sk_C_1) = (sk_B_1)) | (r1_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['108', '118'])).
% 1.26/1.46  thf('120', plain,
% 1.26/1.46      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.26/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.26/1.46  thf('121', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 1.26/1.46      inference('sup+', [status(thm)], ['8', '9'])).
% 1.26/1.46  thf('122', plain,
% 1.26/1.46      (![X14 : $i, X16 : $i]:
% 1.26/1.46         (((k4_xboole_0 @ X14 @ X16) = (k1_xboole_0))
% 1.26/1.46          | ~ (r1_tarski @ X14 @ X16))),
% 1.26/1.46      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.26/1.46  thf('123', plain,
% 1.26/1.46      (((k4_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_xboole_0))),
% 1.26/1.46      inference('sup-', [status(thm)], ['121', '122'])).
% 1.26/1.46  thf('124', plain,
% 1.26/1.46      (![X30 : $i, X31 : $i]: (r1_tarski @ (k4_xboole_0 @ X30 @ X31) @ X30)),
% 1.26/1.46      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.26/1.46  thf('125', plain, ((r1_tarski @ k1_xboole_0 @ sk_B_1)),
% 1.26/1.46      inference('sup+', [status(thm)], ['123', '124'])).
% 1.26/1.46  thf('126', plain,
% 1.26/1.46      (![X25 : $i, X26 : $i]:
% 1.26/1.46         (((k2_xboole_0 @ X26 @ X25) = (X25)) | ~ (r1_tarski @ X26 @ X25))),
% 1.26/1.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.26/1.46  thf('127', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_B_1) = (sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['125', '126'])).
% 1.26/1.46  thf('128', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         (((k2_xboole_0 @ X0 @ sk_B_1) = (sk_B_1)) | ~ (v1_xboole_0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['120', '127'])).
% 1.26/1.46  thf('129', plain,
% 1.26/1.46      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X5))),
% 1.26/1.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.26/1.46  thf('130', plain,
% 1.26/1.46      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['44', '45'])).
% 1.26/1.46  thf('131', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['30', '33'])).
% 1.26/1.46  thf('132', plain,
% 1.26/1.46      (((k3_tarski @ (k1_tarski @ k1_xboole_0)) = (k1_xboole_0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['130', '131'])).
% 1.26/1.46  thf('133', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         (((k3_tarski @ (k1_tarski @ X0)) = (k1_xboole_0))
% 1.26/1.46          | ~ (v1_xboole_0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['129', '132'])).
% 1.26/1.46  thf('134', plain,
% 1.26/1.46      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['44', '45'])).
% 1.26/1.46  thf('135', plain,
% 1.26/1.46      (![X0 : $i]:
% 1.26/1.46         (((k1_xboole_0) = (k2_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.26/1.46      inference('sup+', [status(thm)], ['133', '134'])).
% 1.26/1.46  thf('136', plain,
% 1.26/1.46      ((((sk_C_1) != (k1_xboole_0))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('split', [status(esa)], ['1'])).
% 1.26/1.46  thf('137', plain,
% 1.26/1.46      ((![X0 : $i]:
% 1.26/1.46          (((sk_C_1) != (k2_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X0)))
% 1.26/1.46         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['135', '136'])).
% 1.26/1.46  thf('138', plain,
% 1.26/1.46      (((((sk_C_1) != (sk_B_1))
% 1.26/1.46         | ~ (v1_xboole_0 @ sk_B_1)
% 1.26/1.46         | ~ (v1_xboole_0 @ sk_B_1))) <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('sup-', [status(thm)], ['128', '137'])).
% 1.26/1.46  thf('139', plain,
% 1.26/1.46      (((~ (v1_xboole_0 @ sk_B_1) | ((sk_C_1) != (sk_B_1))))
% 1.26/1.46         <= (~ (((sk_C_1) = (k1_xboole_0))))),
% 1.26/1.46      inference('simplify', [status(thm)], ['138'])).
% 1.26/1.46  thf('140', plain, (~ (((sk_C_1) = (k1_xboole_0)))),
% 1.26/1.46      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 1.26/1.46  thf('141', plain, ((~ (v1_xboole_0 @ sk_B_1) | ((sk_C_1) != (sk_B_1)))),
% 1.26/1.46      inference('simpl_trail', [status(thm)], ['139', '140'])).
% 1.26/1.46  thf('142', plain,
% 1.26/1.46      ((((k1_tarski @ sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup+', [status(thm)], ['20', '21'])).
% 1.26/1.46  thf('143', plain, (((sk_C_1) != (k1_tarski @ sk_A))),
% 1.26/1.46      inference('simpl_trail', [status(thm)], ['59', '69'])).
% 1.26/1.46  thf('144', plain, ((((sk_C_1) != (sk_B_1)) | (v1_xboole_0 @ sk_B_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['142', '143'])).
% 1.26/1.46  thf('145', plain, (((sk_C_1) != (sk_B_1))),
% 1.26/1.46      inference('clc', [status(thm)], ['141', '144'])).
% 1.26/1.46  thf('146', plain, ((r1_xboole_0 @ sk_B_1 @ sk_C_1)),
% 1.26/1.46      inference('simplify_reflect-', [status(thm)], ['119', '145'])).
% 1.26/1.46  thf('147', plain,
% 1.26/1.46      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 1.26/1.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.26/1.46  thf('148', plain,
% 1.26/1.46      (![X10 : $i, X12 : $i, X13 : $i]:
% 1.26/1.46         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 1.26/1.46          | ~ (r1_xboole_0 @ X10 @ X13))),
% 1.26/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.26/1.46  thf('149', plain,
% 1.26/1.46      (![X0 : $i, X1 : $i]:
% 1.26/1.46         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 1.26/1.46      inference('sup-', [status(thm)], ['147', '148'])).
% 1.26/1.46  thf('150', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_B_1 @ sk_C_1))),
% 1.26/1.46      inference('sup-', [status(thm)], ['146', '149'])).
% 1.26/1.46  thf('151', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_1) = (sk_C_1))),
% 1.26/1.46      inference('demod', [status(thm)], ['106', '107'])).
% 1.26/1.46  thf('152', plain, ((v1_xboole_0 @ sk_C_1)),
% 1.26/1.46      inference('demod', [status(thm)], ['150', '151'])).
% 1.26/1.46  thf('153', plain, ($false), inference('demod', [status(thm)], ['75', '152'])).
% 1.26/1.46  
% 1.26/1.46  % SZS output end Refutation
% 1.26/1.46  
% 1.26/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
