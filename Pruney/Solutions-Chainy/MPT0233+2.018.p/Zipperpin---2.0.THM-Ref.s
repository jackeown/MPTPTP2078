%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sPQtqgSKlB

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:39 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  136 (2156 expanded)
%              Number of leaves         :   19 ( 633 expanded)
%              Depth                    :   40
%              Number of atoms          : 1103 (21270 expanded)
%              Number of equality atoms :  183 (3543 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ k1_xboole_0 )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X8: $i] :
      ( ( k2_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('10',plain,
    ( ( k2_tarski @ sk_C @ sk_D )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['4','5','8','9'])).

thf('11',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X25
        = ( k2_tarski @ X23 @ X24 ) )
      | ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25
        = ( k1_tarski @ X23 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k2_tarski @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('13',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ ( k2_tarski @ X23 @ X26 ) )
      | ( X25
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('15',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('17',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ( X28 = X29 )
      | ~ ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('18',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( sk_C = sk_B )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ( X28 = X29 )
      | ~ ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_C = sk_B )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('31',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('33',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('37',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( sk_C = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('49',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_C = sk_B )
      | ( sk_C = sk_B ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C = sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,
    ( ( k2_tarski @ sk_C @ sk_D )
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['10','55'])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('58',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['54'])).

thf('59',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['54'])).

thf('60',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['54'])).

thf('61',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['54'])).

thf('62',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ ( k2_tarski @ X23 @ X26 ) )
      | ( X25
       != ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('64',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X26 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','64'])).

thf('66',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X28 = X27 )
      | ( X28 = X29 )
      | ~ ( r1_tarski @ ( k1_tarski @ X28 ) @ ( k2_tarski @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('67',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('71',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('73',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('77',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('79',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('83',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('87',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['54'])).

thf('93',plain,
    ( ( sk_C = sk_A )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('97',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['93','94'])).

thf('98',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('100',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X26 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('101',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_xboole_0 @ X9 @ ( k4_xboole_0 @ X10 @ X9 ) )
      = ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( k1_tarski @ sk_C )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['56','95','96','97','98','99','108'])).

thf('110',plain,(
    ! [X23: $i,X26: $i] :
      ( r1_tarski @ ( k1_tarski @ X23 ) @ ( k2_tarski @ X23 @ X26 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('111',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('113',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['113','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sPQtqgSKlB
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.89/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.10  % Solved by: fo/fo7.sh
% 0.89/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.10  % done 905 iterations in 0.589s
% 0.89/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.10  % SZS output start Refutation
% 0.89/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.89/1.10  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.89/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.10  thf(sk_C_type, type, sk_C: $i).
% 0.89/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.10  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.89/1.10  thf(sk_D_type, type, sk_D: $i).
% 0.89/1.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.89/1.10  thf(t28_zfmisc_1, conjecture,
% 0.89/1.10    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.10     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.89/1.10          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.89/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.10    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.10        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.89/1.10             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.89/1.10    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.89/1.10  thf('0', plain,
% 0.89/1.10      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(l32_xboole_1, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.89/1.10  thf('1', plain,
% 0.89/1.10      (![X2 : $i, X4 : $i]:
% 0.89/1.10         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.89/1.10      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.89/1.10  thf('2', plain,
% 0.89/1.10      (((k4_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.89/1.10         = (k1_xboole_0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['0', '1'])).
% 0.89/1.10  thf(t39_xboole_1, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.10  thf('3', plain,
% 0.89/1.10      (![X9 : $i, X10 : $i]:
% 0.89/1.10         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.89/1.10           = (k2_xboole_0 @ X9 @ X10))),
% 0.89/1.10      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.10  thf('4', plain,
% 0.89/1.10      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ k1_xboole_0)
% 0.89/1.10         = (k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D) @ (k2_tarski @ sk_A @ sk_B)))),
% 0.89/1.10      inference('sup+', [status(thm)], ['2', '3'])).
% 0.89/1.10  thf(commutativity_k2_xboole_0, axiom,
% 0.89/1.10    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.89/1.10  thf('5', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.10  thf('6', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.10  thf(t1_boole, axiom,
% 0.89/1.10    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.89/1.10  thf('7', plain, (![X8 : $i]: ((k2_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.89/1.10      inference('cnf', [status(esa)], [t1_boole])).
% 0.89/1.10  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.10      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.10  thf('9', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.10      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.10  thf('10', plain,
% 0.89/1.10      (((k2_tarski @ sk_C @ sk_D)
% 0.89/1.10         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.89/1.10      inference('demod', [status(thm)], ['4', '5', '8', '9'])).
% 0.89/1.10  thf('11', plain,
% 0.89/1.10      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf(l45_zfmisc_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.89/1.10       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.89/1.10            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.89/1.10  thf('12', plain,
% 0.89/1.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.10         (((X25) = (k2_tarski @ X23 @ X24))
% 0.89/1.10          | ((X25) = (k1_tarski @ X24))
% 0.89/1.10          | ((X25) = (k1_tarski @ X23))
% 0.89/1.10          | ((X25) = (k1_xboole_0))
% 0.89/1.10          | ~ (r1_tarski @ X25 @ (k2_tarski @ X23 @ X24)))),
% 0.89/1.10      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.89/1.10  thf('13', plain,
% 0.89/1.10      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.10  thf('14', plain,
% 0.89/1.10      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.89/1.10         ((r1_tarski @ X25 @ (k2_tarski @ X23 @ X26))
% 0.89/1.10          | ((X25) != (k1_tarski @ X23)))),
% 0.89/1.10      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.89/1.10  thf('15', plain,
% 0.89/1.10      (![X23 : $i, X26 : $i]:
% 0.89/1.10         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.10      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.10  thf('16', plain,
% 0.89/1.10      (((r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup+', [status(thm)], ['13', '15'])).
% 0.89/1.10  thf(t25_zfmisc_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.89/1.10          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.89/1.10  thf('17', plain,
% 0.89/1.10      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.89/1.10         (((X28) = (X27))
% 0.89/1.10          | ((X28) = (X29))
% 0.89/1.10          | ~ (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X27 @ X29)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.89/1.10  thf('18', plain,
% 0.89/1.10      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.89/1.10        | ((sk_C) = (sk_B))
% 0.89/1.10        | ((sk_C) = (sk_A)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['16', '17'])).
% 0.89/1.10  thf('19', plain, (((sk_A) != (sk_C))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('20', plain,
% 0.89/1.10      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.89/1.10        | ((sk_C) = (sk_B)))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.89/1.10  thf('21', plain,
% 0.89/1.10      (![X23 : $i, X26 : $i]:
% 0.89/1.10         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.10      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.10  thf('22', plain,
% 0.89/1.10      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.89/1.10        | ((sk_C) = (sk_B))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup+', [status(thm)], ['20', '21'])).
% 0.89/1.10  thf(t69_enumset1, axiom,
% 0.89/1.10    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.89/1.10  thf('23', plain,
% 0.89/1.10      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.89/1.10      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.89/1.10  thf('24', plain,
% 0.89/1.10      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.89/1.10         (((X28) = (X27))
% 0.89/1.10          | ((X28) = (X29))
% 0.89/1.10          | ~ (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X27 @ X29)))),
% 0.89/1.10      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.89/1.10  thf('25', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]:
% 0.89/1.10         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.89/1.10          | ((X1) = (X0))
% 0.89/1.10          | ((X1) = (X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.10  thf('26', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]:
% 0.89/1.10         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.10      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.10  thf('27', plain,
% 0.89/1.10      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((sk_C) = (sk_B))
% 0.89/1.10        | ((sk_A) = (sk_D)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['22', '26'])).
% 0.89/1.10  thf('28', plain, (((sk_A) != (sk_D))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('29', plain,
% 0.89/1.10      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.10        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.10        | ((sk_C) = (sk_B)))),
% 0.89/1.10      inference('simplify_reflect-', [status(thm)], ['27', '28'])).
% 0.89/1.10  thf('30', plain,
% 0.89/1.10      (![X23 : $i, X26 : $i]:
% 0.89/1.10         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.10      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.10  thf('31', plain,
% 0.89/1.10      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.89/1.11        | ((sk_C) = (sk_B))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['29', '30'])).
% 0.89/1.11  thf('32', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('33', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.11        | ((sk_C) = (sk_B))
% 0.89/1.11        | ((sk_A) = (sk_C)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['31', '32'])).
% 0.89/1.11  thf('34', plain, (((sk_A) != (sk_C))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('35', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['33', '34'])).
% 0.89/1.11  thf('36', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.11  thf('37', plain,
% 0.89/1.11      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_C) = (sk_B)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['35', '36'])).
% 0.89/1.11  thf('38', plain,
% 0.89/1.11      (![X2 : $i, X4 : $i]:
% 0.89/1.11         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.89/1.11      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.89/1.11  thf('39', plain,
% 0.89/1.11      ((((sk_C) = (sk_B))
% 0.89/1.11        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.11  thf('40', plain,
% 0.89/1.11      (![X9 : $i, X10 : $i]:
% 0.89/1.11         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.89/1.11           = (k2_xboole_0 @ X9 @ X10))),
% 0.89/1.11      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.11  thf('41', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.11  thf('42', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['40', '41'])).
% 0.89/1.11  thf('43', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.11  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['42', '43'])).
% 0.89/1.11  thf('45', plain,
% 0.89/1.11      ((((sk_C) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.89/1.11      inference('demod', [status(thm)], ['39', '44'])).
% 0.89/1.11  thf('46', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('47', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.89/1.11          | ((sk_C) = (sk_B))
% 0.89/1.11          | ((sk_A) = (X0)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['45', '46'])).
% 0.89/1.11  thf('48', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.11  thf(t7_xboole_1, axiom,
% 0.89/1.11    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.89/1.11  thf('49', plain,
% 0.89/1.11      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 0.89/1.11      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.89/1.11  thf('50', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.89/1.11      inference('sup+', [status(thm)], ['48', '49'])).
% 0.89/1.11  thf('51', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.89/1.11      inference('demod', [status(thm)], ['47', '50'])).
% 0.89/1.11  thf('52', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.89/1.11      inference('demod', [status(thm)], ['47', '50'])).
% 0.89/1.11  thf('53', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X0) = (X1)) | ((sk_C) = (sk_B)) | ((sk_C) = (sk_B)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['51', '52'])).
% 0.89/1.11  thf('54', plain, (![X0 : $i, X1 : $i]: (((sk_C) = (sk_B)) | ((X0) = (X1)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['53'])).
% 0.89/1.11  thf('55', plain, (((sk_C) = (sk_B))),
% 0.89/1.11      inference('condensation', [status(thm)], ['54'])).
% 0.89/1.11  thf('56', plain,
% 0.89/1.11      (((k2_tarski @ sk_C @ sk_D)
% 0.89/1.11         = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.89/1.11      inference('demod', [status(thm)], ['10', '55'])).
% 0.89/1.11  thf('57', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['11', '12'])).
% 0.89/1.11  thf('58', plain, (((sk_C) = (sk_B))),
% 0.89/1.11      inference('condensation', [status(thm)], ['54'])).
% 0.89/1.11  thf('59', plain, (((sk_C) = (sk_B))),
% 0.89/1.11      inference('condensation', [status(thm)], ['54'])).
% 0.89/1.11  thf('60', plain, (((sk_C) = (sk_B))),
% 0.89/1.11      inference('condensation', [status(thm)], ['54'])).
% 0.89/1.11  thf('61', plain, (((sk_C) = (sk_B))),
% 0.89/1.11      inference('condensation', [status(thm)], ['54'])).
% 0.89/1.11  thf('62', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k2_tarski @ sk_C @ sk_D)))),
% 0.89/1.11      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.89/1.11  thf('63', plain,
% 0.89/1.11      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.89/1.11         ((r1_tarski @ X25 @ (k2_tarski @ X23 @ X26))
% 0.89/1.11          | ((X25) != (k1_tarski @ X26)))),
% 0.89/1.11      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.89/1.11  thf('64', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X26) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['63'])).
% 0.89/1.11  thf('65', plain,
% 0.89/1.11      (((r1_tarski @ (k1_tarski @ sk_D) @ (k2_tarski @ sk_A @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['62', '64'])).
% 0.89/1.11  thf('66', plain,
% 0.89/1.11      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.89/1.11         (((X28) = (X27))
% 0.89/1.11          | ((X28) = (X29))
% 0.89/1.11          | ~ (r1_tarski @ (k1_tarski @ X28) @ (k2_tarski @ X27 @ X29)))),
% 0.89/1.11      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.89/1.11  thf('67', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.89/1.11        | ((sk_D) = (sk_C))
% 0.89/1.11        | ((sk_D) = (sk_A)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['65', '66'])).
% 0.89/1.11  thf('68', plain, (((sk_A) != (sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('69', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.89/1.11        | ((sk_D) = (sk_C)))),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['67', '68'])).
% 0.89/1.11  thf('70', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.11  thf('71', plain,
% 0.89/1.11      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.89/1.11        | ((sk_D) = (sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['69', '70'])).
% 0.89/1.11  thf('72', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('73', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((sk_D) = (sk_C))
% 0.89/1.11        | ((sk_A) = (sk_D)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['71', '72'])).
% 0.89/1.11  thf('74', plain, (((sk_A) != (sk_D))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('75', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.89/1.11        | ((sk_D) = (sk_C)))),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.89/1.11  thf('76', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.11  thf('77', plain,
% 0.89/1.11      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.89/1.11        | ((sk_D) = (sk_C))
% 0.89/1.11        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['75', '76'])).
% 0.89/1.11  thf('78', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('79', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.89/1.11        | ((sk_D) = (sk_C))
% 0.89/1.11        | ((sk_A) = (sk_C)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['77', '78'])).
% 0.89/1.11  thf('80', plain, (((sk_A) != (sk_C))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('81', plain,
% 0.89/1.11      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)) | ((sk_D) = (sk_C)))),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['79', '80'])).
% 0.89/1.11  thf('82', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.11  thf('83', plain,
% 0.89/1.11      (![X2 : $i, X4 : $i]:
% 0.89/1.11         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.89/1.11      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.89/1.11  thf('84', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((k4_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.89/1.11           = (k1_xboole_0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['82', '83'])).
% 0.89/1.11  thf('85', plain,
% 0.89/1.11      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))
% 0.89/1.11        | ((sk_D) = (sk_C)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['81', '84'])).
% 0.89/1.11  thf('86', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['42', '43'])).
% 0.89/1.11  thf('87', plain,
% 0.89/1.11      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ((sk_D) = (sk_C)))),
% 0.89/1.11      inference('demod', [status(thm)], ['85', '86'])).
% 0.89/1.11  thf('88', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('89', plain,
% 0.89/1.11      (![X0 : $i]:
% 0.89/1.11         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.89/1.11          | ((sk_D) = (sk_C))
% 0.89/1.11          | ((sk_A) = (X0)))),
% 0.89/1.11      inference('sup-', [status(thm)], ['87', '88'])).
% 0.89/1.11  thf('90', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.89/1.11      inference('sup+', [status(thm)], ['48', '49'])).
% 0.89/1.11  thf('91', plain, (![X0 : $i]: (((sk_D) = (sk_C)) | ((sk_A) = (X0)))),
% 0.89/1.11      inference('demod', [status(thm)], ['89', '90'])).
% 0.89/1.11  thf('92', plain, (((sk_C) = (sk_B))),
% 0.89/1.11      inference('condensation', [status(thm)], ['54'])).
% 0.89/1.11  thf('93', plain, ((((sk_C) = (sk_A)) | ((sk_D) = (sk_C)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['91', '92'])).
% 0.89/1.11  thf('94', plain, (((sk_A) != (sk_C))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('95', plain, (((sk_D) = (sk_C))),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.89/1.11  thf('96', plain,
% 0.89/1.11      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.89/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.89/1.11  thf('97', plain, (((sk_D) = (sk_C))),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['93', '94'])).
% 0.89/1.11  thf('98', plain,
% 0.89/1.11      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.89/1.11      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.89/1.11  thf('99', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.11  thf('100', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X26) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['63'])).
% 0.89/1.11  thf('101', plain,
% 0.89/1.11      (![X2 : $i, X4 : $i]:
% 0.89/1.11         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 0.89/1.11      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.89/1.11  thf('102', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.89/1.11           = (k1_xboole_0))),
% 0.89/1.11      inference('sup-', [status(thm)], ['100', '101'])).
% 0.89/1.11  thf('103', plain,
% 0.89/1.11      (![X9 : $i, X10 : $i]:
% 0.89/1.11         ((k2_xboole_0 @ X9 @ (k4_xboole_0 @ X10 @ X9))
% 0.89/1.11           = (k2_xboole_0 @ X9 @ X10))),
% 0.89/1.11      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.89/1.11  thf('104', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ k1_xboole_0)
% 0.89/1.11           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('sup+', [status(thm)], ['102', '103'])).
% 0.89/1.11  thf('105', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.11  thf('106', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.89/1.11      inference('sup+', [status(thm)], ['6', '7'])).
% 0.89/1.11  thf('107', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.89/1.11      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.89/1.11  thf('108', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         ((k2_tarski @ X1 @ X0)
% 0.89/1.11           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0)))),
% 0.89/1.11      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.89/1.11  thf('109', plain, (((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_C))),
% 0.89/1.11      inference('demod', [status(thm)],
% 0.89/1.11                ['56', '95', '96', '97', '98', '99', '108'])).
% 0.89/1.11  thf('110', plain,
% 0.89/1.11      (![X23 : $i, X26 : $i]:
% 0.89/1.11         (r1_tarski @ (k1_tarski @ X23) @ (k2_tarski @ X23 @ X26))),
% 0.89/1.11      inference('simplify', [status(thm)], ['14'])).
% 0.89/1.11  thf('111', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.89/1.11      inference('sup+', [status(thm)], ['109', '110'])).
% 0.89/1.11  thf('112', plain,
% 0.89/1.11      (![X0 : $i, X1 : $i]:
% 0.89/1.11         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.89/1.11      inference('simplify', [status(thm)], ['25'])).
% 0.89/1.11  thf('113', plain, (((sk_A) = (sk_C))),
% 0.89/1.11      inference('sup-', [status(thm)], ['111', '112'])).
% 0.89/1.11  thf('114', plain, (((sk_A) != (sk_C))),
% 0.89/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.11  thf('115', plain, ($false),
% 0.89/1.11      inference('simplify_reflect-', [status(thm)], ['113', '114'])).
% 0.89/1.11  
% 0.89/1.11  % SZS output end Refutation
% 0.89/1.11  
% 0.89/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
