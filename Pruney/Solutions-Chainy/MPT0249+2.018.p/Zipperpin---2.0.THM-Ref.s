%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZHDL6MYvps

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:41 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  145 (3792 expanded)
%              Number of leaves         :   30 (1226 expanded)
%              Depth                    :   31
%              Number of atoms          :  995 (31996 expanded)
%              Number of equality atoms :  129 (4955 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) )
      = ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X29 @ X30 ) @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('11',plain,(
    ! [X28: $i] :
      ( ( k4_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','8','11'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X33 )
      | ( X34 = X31 )
      | ( X33
       != ( k1_tarski @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('21',plain,(
    ! [X31: $i,X34: $i] :
      ( ( X34 = X31 )
      | ~ ( r2_hidden @ X34 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( ( sk_B @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( sk_B @ sk_B_1 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('30',plain,(
    ! [X116: $i,X117: $i] :
      ( ( ( k3_xboole_0 @ X117 @ ( k1_tarski @ X116 ) )
        = ( k1_tarski @ X116 ) )
      | ~ ( r2_hidden @ X116 @ X117 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('36',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_xboole_0 @ X29 @ X30 )
      = ( k5_xboole_0 @ X29 @ ( k5_xboole_0 @ X30 @ ( k2_xboole_0 @ X29 @ X30 ) ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = ( k5_xboole_0 @ sk_B_1 @ ( k5_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X25 @ X26 ) @ X27 )
      = ( k5_xboole_0 @ X25 @ ( k5_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X2 @ X1 ) )
      = ( k5_xboole_0 @ X2 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X28: $i] :
      ( ( k5_xboole_0 @ X28 @ X28 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('46',plain,(
    ! [X22: $i] :
      ( ( k5_xboole_0 @ X22 @ k1_xboole_0 )
      = X22 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('53',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('54',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['51','55'])).

thf('57',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['39','50'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('62',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('63',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['39','50'])).

thf('67',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('72',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('75',plain,(
    ! [X81: $i] :
      ( ( k2_tarski @ X81 @ X81 )
      = ( k1_tarski @ X81 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('76',plain,(
    ! [X121: $i,X122: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X121 @ X122 ) )
      = ( k2_xboole_0 @ X121 @ X122 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('78',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( k3_tarski @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    = sk_A ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('82',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['73','82'])).

thf('84',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','83'])).

thf('85',plain,(
    r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['69','84'])).

thf('86',plain,(
    ! [X116: $i,X117: $i] :
      ( ( ( k3_xboole_0 @ X117 @ ( k1_tarski @ X116 ) )
        = ( k1_tarski @ X116 ) )
      | ~ ( r2_hidden @ X116 @ X117 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('87',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) )
    = ( k1_tarski @ ( k3_tarski @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['31','32','33','34'])).

thf('90',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['80','81'])).

thf('92',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['90','91'])).

thf('94',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['87','92','93'])).

thf('95',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['95'])).

thf('98',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference(demod,[status(thm)],['39','50'])).

thf('99',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( sk_C_2
        = ( k3_xboole_0 @ sk_C_2 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_C_2 @ X0 @ sk_C_2 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['97','100'])).

thf('102',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('103',plain,
    ( ( sk_C_2
      = ( k3_xboole_0 @ sk_C_2 @ sk_B_1 ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2
      = ( k3_xboole_0 @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['87','92','93'])).

thf('105',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['87','92','93'])).

thf('106',plain,
    ( ( sk_C_2 = sk_B_1 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_B_1 ) ),
    inference(demod,[status(thm)],['103','104','105'])).

thf('107',plain,
    ( ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 )
    | ( sk_C_2 = sk_B_1 ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ~ ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2 ) @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['107','108'])).

thf('110',plain,
    ( sk_C_2
    = ( k3_xboole_0 @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','109'])).

thf('111',plain,(
    sk_C_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['94','110'])).

thf('112',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['111','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZHDL6MYvps
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 1.51/1.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.51/1.71  % Solved by: fo/fo7.sh
% 1.51/1.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.51/1.71  % done 2362 iterations in 1.258s
% 1.51/1.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.51/1.71  % SZS output start Refutation
% 1.51/1.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.51/1.71  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.51/1.71  thf(sk_B_type, type, sk_B: $i > $i).
% 1.51/1.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.51/1.71  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.51/1.71  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.51/1.71  thf(sk_A_type, type, sk_A: $i).
% 1.51/1.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.51/1.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.51/1.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.51/1.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.51/1.71  thf(t7_xboole_0, axiom,
% 1.51/1.71    (![A:$i]:
% 1.51/1.71     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.51/1.71          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 1.51/1.71  thf('0', plain,
% 1.51/1.71      (![X10 : $i]:
% 1.51/1.71         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.51/1.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.51/1.71  thf(t6_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.71  thf('1', plain,
% 1.51/1.71      (![X23 : $i, X24 : $i]:
% 1.51/1.71         ((k2_xboole_0 @ X23 @ (k2_xboole_0 @ X23 @ X24))
% 1.51/1.71           = (k2_xboole_0 @ X23 @ X24))),
% 1.51/1.71      inference('cnf', [status(esa)], [t6_xboole_1])).
% 1.51/1.71  thf(t95_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k3_xboole_0 @ A @ B ) =
% 1.51/1.71       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.51/1.71  thf('2', plain,
% 1.51/1.71      (![X29 : $i, X30 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X29 @ X30)
% 1.51/1.71           = (k5_xboole_0 @ (k5_xboole_0 @ X29 @ X30) @ 
% 1.51/1.71              (k2_xboole_0 @ X29 @ X30)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.51/1.71  thf(t91_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.51/1.71       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.51/1.71  thf('3', plain,
% 1.51/1.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.51/1.71           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.51/1.71  thf('4', plain,
% 1.51/1.71      (![X29 : $i, X30 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X29 @ X30)
% 1.51/1.71           = (k5_xboole_0 @ X29 @ 
% 1.51/1.71              (k5_xboole_0 @ X30 @ (k2_xboole_0 @ X29 @ X30))))),
% 1.51/1.71      inference('demod', [status(thm)], ['2', '3'])).
% 1.51/1.71  thf('5', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.51/1.71           = (k5_xboole_0 @ X1 @ 
% 1.51/1.71              (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X1 @ X0))))),
% 1.51/1.71      inference('sup+', [status(thm)], ['1', '4'])).
% 1.51/1.71  thf(idempotence_k3_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.51/1.71  thf('6', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 1.51/1.71      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.51/1.71  thf(t100_xboole_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.51/1.71  thf('7', plain,
% 1.51/1.71      (![X14 : $i, X15 : $i]:
% 1.51/1.71         ((k4_xboole_0 @ X14 @ X15)
% 1.51/1.71           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.51/1.71  thf('8', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['6', '7'])).
% 1.51/1.71  thf(t92_xboole_1, axiom,
% 1.51/1.71    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.51/1.71  thf('9', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.51/1.71  thf('10', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['6', '7'])).
% 1.51/1.71  thf('11', plain, (![X28 : $i]: ((k4_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['9', '10'])).
% 1.51/1.71  thf('12', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0))
% 1.51/1.71           = (k5_xboole_0 @ X1 @ k1_xboole_0))),
% 1.51/1.71      inference('demod', [status(thm)], ['5', '8', '11'])).
% 1.51/1.71  thf(t5_boole, axiom,
% 1.51/1.71    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.51/1.71  thf('13', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.51/1.71      inference('cnf', [status(esa)], [t5_boole])).
% 1.51/1.71  thf('14', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.51/1.71      inference('demod', [status(thm)], ['12', '13'])).
% 1.51/1.71  thf(d4_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.51/1.71       ( ![D:$i]:
% 1.51/1.71         ( ( r2_hidden @ D @ C ) <=>
% 1.51/1.71           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.51/1.71  thf('15', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X6 @ X5)
% 1.51/1.71          | (r2_hidden @ X6 @ X4)
% 1.51/1.71          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.51/1.71  thf('16', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.51/1.71         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['15'])).
% 1.51/1.71  thf('17', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X2 @ X0) | (r2_hidden @ X2 @ (k2_xboole_0 @ X0 @ X1)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['14', '16'])).
% 1.51/1.71  thf('18', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (((X0) = (k1_xboole_0))
% 1.51/1.71          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X0 @ X1)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['0', '17'])).
% 1.51/1.71  thf(t44_zfmisc_1, conjecture,
% 1.51/1.71    (![A:$i,B:$i,C:$i]:
% 1.51/1.71     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.51/1.71          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.51/1.71          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 1.51/1.71  thf(zf_stmt_0, negated_conjecture,
% 1.51/1.71    (~( ![A:$i,B:$i,C:$i]:
% 1.51/1.71        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 1.51/1.71             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.51/1.71             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 1.51/1.71    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 1.51/1.71  thf('19', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(d1_tarski, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 1.51/1.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 1.51/1.71  thf('20', plain,
% 1.51/1.71      (![X31 : $i, X33 : $i, X34 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X34 @ X33)
% 1.51/1.71          | ((X34) = (X31))
% 1.51/1.71          | ((X33) != (k1_tarski @ X31)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d1_tarski])).
% 1.51/1.71  thf('21', plain,
% 1.51/1.71      (![X31 : $i, X34 : $i]:
% 1.51/1.71         (((X34) = (X31)) | ~ (r2_hidden @ X34 @ (k1_tarski @ X31)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['20'])).
% 1.51/1.71  thf('22', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 1.51/1.71          | ((X0) = (sk_A)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['19', '21'])).
% 1.51/1.71  thf('23', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_B @ sk_B_1) = (sk_A)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['18', '22'])).
% 1.51/1.71  thf('24', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('25', plain, (((sk_B @ sk_B_1) = (sk_A))),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 1.51/1.71  thf('26', plain,
% 1.51/1.71      (![X10 : $i]:
% 1.51/1.71         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.51/1.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.51/1.71  thf('27', plain,
% 1.51/1.71      (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['25', '26'])).
% 1.51/1.71  thf('28', plain, (((sk_B_1) != (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('29', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 1.51/1.71  thf(l31_zfmisc_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( r2_hidden @ A @ B ) =>
% 1.51/1.71       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 1.51/1.71  thf('30', plain,
% 1.51/1.71      (![X116 : $i, X117 : $i]:
% 1.51/1.71         (((k3_xboole_0 @ X117 @ (k1_tarski @ X116)) = (k1_tarski @ X116))
% 1.51/1.71          | ~ (r2_hidden @ X116 @ X117))),
% 1.51/1.71      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.51/1.71  thf('31', plain,
% 1.51/1.71      (((k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 1.51/1.71      inference('sup-', [status(thm)], ['29', '30'])).
% 1.51/1.71  thf('32', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('33', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 1.51/1.71      inference('demod', [status(thm)], ['12', '13'])).
% 1.51/1.71  thf('34', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('35', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.51/1.71  thf('36', plain,
% 1.51/1.71      (![X29 : $i, X30 : $i]:
% 1.51/1.71         ((k3_xboole_0 @ X29 @ X30)
% 1.51/1.71           = (k5_xboole_0 @ X29 @ 
% 1.51/1.71              (k5_xboole_0 @ X30 @ (k2_xboole_0 @ X29 @ X30))))),
% 1.51/1.71      inference('demod', [status(thm)], ['2', '3'])).
% 1.51/1.71  thf('37', plain,
% 1.51/1.71      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.51/1.71         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_C_2 @ sk_B_1)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['35', '36'])).
% 1.51/1.71  thf(commutativity_k5_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.51/1.71  thf('38', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.51/1.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.51/1.71  thf('39', plain,
% 1.51/1.71      (((k3_xboole_0 @ sk_B_1 @ sk_C_2)
% 1.51/1.71         = (k5_xboole_0 @ sk_B_1 @ (k5_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 1.51/1.71      inference('demod', [status(thm)], ['37', '38'])).
% 1.51/1.71  thf('40', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['6', '7'])).
% 1.51/1.71  thf('41', plain,
% 1.51/1.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ (k5_xboole_0 @ X25 @ X26) @ X27)
% 1.51/1.71           = (k5_xboole_0 @ X25 @ (k5_xboole_0 @ X26 @ X27)))),
% 1.51/1.71      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.51/1.71  thf('42', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.51/1.71      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.51/1.71  thf('43', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ X0 @ (k5_xboole_0 @ X2 @ X1))
% 1.51/1.71           = (k5_xboole_0 @ X2 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['41', '42'])).
% 1.51/1.71  thf('44', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0))
% 1.51/1.71           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['40', '43'])).
% 1.51/1.71  thf('45', plain, (![X28 : $i]: ((k5_xboole_0 @ X28 @ X28) = (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.51/1.71  thf('46', plain, (![X22 : $i]: ((k5_xboole_0 @ X22 @ k1_xboole_0) = (X22))),
% 1.51/1.71      inference('cnf', [status(esa)], [t5_boole])).
% 1.51/1.71  thf('47', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ X0)) = (X1))),
% 1.51/1.71      inference('sup+', [status(thm)], ['45', '46'])).
% 1.51/1.71  thf('48', plain,
% 1.51/1.71      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['6', '7'])).
% 1.51/1.71  thf('49', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((k5_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (X1))),
% 1.51/1.71      inference('demod', [status(thm)], ['47', '48'])).
% 1.51/1.71  thf('50', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X1)))),
% 1.51/1.71      inference('demod', [status(thm)], ['44', '49'])).
% 1.51/1.71  thf('51', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['39', '50'])).
% 1.51/1.71  thf('52', plain,
% 1.51/1.71      (![X10 : $i]:
% 1.51/1.71         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.51/1.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.51/1.71  thf('53', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X6 @ X5)
% 1.51/1.71          | (r2_hidden @ X6 @ X3)
% 1.51/1.71          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.51/1.71  thf('54', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.51/1.71         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['53'])).
% 1.51/1.71  thf('55', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 1.51/1.71          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['52', '54'])).
% 1.51/1.71  thf('56', plain,
% 1.51/1.71      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 1.51/1.71        | ((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (k1_xboole_0)))),
% 1.51/1.71      inference('sup+', [status(thm)], ['51', '55'])).
% 1.51/1.71  thf('57', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['39', '50'])).
% 1.51/1.71  thf('58', plain,
% 1.51/1.71      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_C_2) = (k1_xboole_0)))),
% 1.51/1.71      inference('demod', [status(thm)], ['56', '57'])).
% 1.51/1.71  thf('59', plain, (((sk_C_2) != (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('60', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.51/1.71  thf('61', plain,
% 1.51/1.71      (![X10 : $i]:
% 1.51/1.71         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 1.51/1.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 1.51/1.71  thf('62', plain,
% 1.51/1.71      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X2 @ X3)
% 1.51/1.71          | ~ (r2_hidden @ X2 @ X4)
% 1.51/1.71          | (r2_hidden @ X2 @ X5)
% 1.51/1.71          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 1.51/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.51/1.71  thf('63', plain,
% 1.51/1.71      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.51/1.71         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 1.51/1.71          | ~ (r2_hidden @ X2 @ X4)
% 1.51/1.71          | ~ (r2_hidden @ X2 @ X3))),
% 1.51/1.71      inference('simplify', [status(thm)], ['62'])).
% 1.51/1.71  thf('64', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         (((X0) = (k1_xboole_0))
% 1.51/1.71          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 1.51/1.71          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['61', '63'])).
% 1.51/1.71  thf('65', plain,
% 1.51/1.71      (((r2_hidden @ (sk_B @ sk_C_2) @ (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 1.51/1.71        | ((sk_C_2) = (k1_xboole_0)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['60', '64'])).
% 1.51/1.71  thf('66', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['39', '50'])).
% 1.51/1.71  thf('67', plain,
% 1.51/1.71      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_C_2) | ((sk_C_2) = (k1_xboole_0)))),
% 1.51/1.71      inference('demod', [status(thm)], ['65', '66'])).
% 1.51/1.71  thf('68', plain, (((sk_C_2) != (k1_xboole_0))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('69', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_C_2)),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 1.51/1.71  thf('70', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['58', '59'])).
% 1.51/1.71  thf('71', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 1.51/1.71          | ((X0) = (sk_A)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['19', '21'])).
% 1.51/1.71  thf('72', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.51/1.71  thf('73', plain,
% 1.51/1.71      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 1.51/1.71      inference('demod', [status(thm)], ['71', '72'])).
% 1.51/1.71  thf('74', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf(t69_enumset1, axiom,
% 1.51/1.71    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.51/1.71  thf('75', plain,
% 1.51/1.71      (![X81 : $i]: ((k2_tarski @ X81 @ X81) = (k1_tarski @ X81))),
% 1.51/1.71      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.51/1.71  thf(l51_zfmisc_1, axiom,
% 1.51/1.71    (![A:$i,B:$i]:
% 1.51/1.71     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.51/1.71  thf('76', plain,
% 1.51/1.71      (![X121 : $i, X122 : $i]:
% 1.51/1.71         ((k3_tarski @ (k2_tarski @ X121 @ X122)) = (k2_xboole_0 @ X121 @ X122))),
% 1.51/1.71      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.51/1.71  thf('77', plain,
% 1.51/1.71      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 1.51/1.71      inference('sup+', [status(thm)], ['75', '76'])).
% 1.51/1.71  thf(idempotence_k2_xboole_0, axiom,
% 1.51/1.71    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 1.51/1.71  thf('78', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ X8) = (X8))),
% 1.51/1.71      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 1.51/1.71  thf('79', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 1.51/1.71      inference('demod', [status(thm)], ['77', '78'])).
% 1.51/1.71  thf('80', plain, (((k3_tarski @ (k2_xboole_0 @ sk_B_1 @ sk_C_2)) = (sk_A))),
% 1.51/1.71      inference('sup+', [status(thm)], ['74', '79'])).
% 1.51/1.71  thf('81', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.51/1.71  thf('82', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.51/1.71      inference('demod', [status(thm)], ['80', '81'])).
% 1.51/1.71  thf('83', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 1.51/1.71      inference('demod', [status(thm)], ['73', '82'])).
% 1.51/1.71  thf('84', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['70', '83'])).
% 1.51/1.71  thf('85', plain, ((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)),
% 1.51/1.71      inference('demod', [status(thm)], ['69', '84'])).
% 1.51/1.71  thf('86', plain,
% 1.51/1.71      (![X116 : $i, X117 : $i]:
% 1.51/1.71         (((k3_xboole_0 @ X117 @ (k1_tarski @ X116)) = (k1_tarski @ X116))
% 1.51/1.71          | ~ (r2_hidden @ X116 @ X117))),
% 1.51/1.71      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 1.51/1.71  thf('87', plain,
% 1.51/1.71      (((k3_xboole_0 @ sk_C_2 @ (k1_tarski @ (k3_tarski @ sk_B_1)))
% 1.51/1.71         = (k1_tarski @ (k3_tarski @ sk_B_1)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['85', '86'])).
% 1.51/1.71  thf('88', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('89', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['31', '32', '33', '34'])).
% 1.51/1.71  thf('90', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 1.51/1.71      inference('demod', [status(thm)], ['88', '89'])).
% 1.51/1.71  thf('91', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 1.51/1.71      inference('demod', [status(thm)], ['80', '81'])).
% 1.51/1.71  thf('92', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 1.51/1.71      inference('demod', [status(thm)], ['90', '91'])).
% 1.51/1.71  thf('93', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 1.51/1.71      inference('demod', [status(thm)], ['90', '91'])).
% 1.51/1.71  thf('94', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 1.51/1.71      inference('demod', [status(thm)], ['87', '92', '93'])).
% 1.51/1.71  thf('95', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.51/1.71         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.51/1.71          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.51/1.71          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.51/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.51/1.71  thf('96', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.71          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.51/1.71      inference('eq_fact', [status(thm)], ['95'])).
% 1.51/1.71  thf('97', plain,
% 1.51/1.71      (![X0 : $i, X1 : $i]:
% 1.51/1.71         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 1.51/1.71          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 1.51/1.71      inference('eq_fact', [status(thm)], ['95'])).
% 1.51/1.71  thf('98', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 1.51/1.71      inference('demod', [status(thm)], ['39', '50'])).
% 1.51/1.71  thf('99', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 1.51/1.71         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['53'])).
% 1.51/1.71  thf('100', plain,
% 1.51/1.71      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_2) | (r2_hidden @ X0 @ sk_B_1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['98', '99'])).
% 1.51/1.71  thf('101', plain,
% 1.51/1.71      (![X0 : $i]:
% 1.51/1.71         (((sk_C_2) = (k3_xboole_0 @ sk_C_2 @ X0))
% 1.51/1.71          | (r2_hidden @ (sk_D @ sk_C_2 @ X0 @ sk_C_2) @ sk_B_1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['97', '100'])).
% 1.51/1.71  thf('102', plain,
% 1.51/1.71      (![X3 : $i, X4 : $i, X7 : $i]:
% 1.51/1.71         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 1.51/1.71          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 1.51/1.71          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 1.51/1.71          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 1.51/1.71      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.51/1.71  thf('103', plain,
% 1.51/1.71      ((((sk_C_2) = (k3_xboole_0 @ sk_C_2 @ sk_B_1))
% 1.51/1.71        | ~ (r2_hidden @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2) @ sk_C_2)
% 1.51/1.71        | ~ (r2_hidden @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2) @ sk_C_2)
% 1.51/1.71        | ((sk_C_2) = (k3_xboole_0 @ sk_C_2 @ sk_B_1)))),
% 1.51/1.71      inference('sup-', [status(thm)], ['101', '102'])).
% 1.51/1.71  thf('104', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 1.51/1.71      inference('demod', [status(thm)], ['87', '92', '93'])).
% 1.51/1.71  thf('105', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_B_1))),
% 1.51/1.71      inference('demod', [status(thm)], ['87', '92', '93'])).
% 1.51/1.71  thf('106', plain,
% 1.51/1.71      ((((sk_C_2) = (sk_B_1))
% 1.51/1.71        | ~ (r2_hidden @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2) @ sk_C_2)
% 1.51/1.71        | ~ (r2_hidden @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2) @ sk_C_2)
% 1.51/1.71        | ((sk_C_2) = (sk_B_1)))),
% 1.51/1.71      inference('demod', [status(thm)], ['103', '104', '105'])).
% 1.51/1.71  thf('107', plain,
% 1.51/1.71      ((~ (r2_hidden @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2) @ sk_C_2)
% 1.51/1.71        | ((sk_C_2) = (sk_B_1)))),
% 1.51/1.71      inference('simplify', [status(thm)], ['106'])).
% 1.51/1.71  thf('108', plain, (((sk_B_1) != (sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('109', plain,
% 1.51/1.71      (~ (r2_hidden @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_C_2) @ sk_C_2)),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['107', '108'])).
% 1.51/1.71  thf('110', plain, (((sk_C_2) = (k3_xboole_0 @ sk_C_2 @ sk_B_1))),
% 1.51/1.71      inference('sup-', [status(thm)], ['96', '109'])).
% 1.51/1.71  thf('111', plain, (((sk_C_2) = (sk_B_1))),
% 1.51/1.71      inference('sup+', [status(thm)], ['94', '110'])).
% 1.51/1.71  thf('112', plain, (((sk_B_1) != (sk_C_2))),
% 1.51/1.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.51/1.71  thf('113', plain, ($false),
% 1.51/1.71      inference('simplify_reflect-', [status(thm)], ['111', '112'])).
% 1.51/1.71  
% 1.51/1.71  % SZS output end Refutation
% 1.51/1.71  
% 1.51/1.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
