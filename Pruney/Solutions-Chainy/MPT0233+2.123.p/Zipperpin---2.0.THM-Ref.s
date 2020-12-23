%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wIVzMb2ySl

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:50 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  116 (1269 expanded)
%              Number of leaves         :   15 ( 365 expanded)
%              Depth                    :   39
%              Number of atoms          :  971 (13396 expanded)
%              Number of equality atoms :  165 (2210 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X16
        = ( k2_tarski @ X14 @ X15 ) )
      | ( X16
        = ( k1_tarski @ X15 ) )
      | ( X16
        = ( k1_tarski @ X14 ) )
      | ( X16 = k1_xboole_0 )
      | ~ ( r1_tarski @ X16 @ ( k2_tarski @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('5',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k2_tarski @ X14 @ X17 ) )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_C ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf(t25_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 = X18 )
      | ( X19 = X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('10',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( sk_C = sk_B )
    | ( sk_C = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('14',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 = X18 )
      | ( X19 = X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_C = sk_B )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_C = sk_B )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('25',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = sk_B ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k2_tarski @ X14 @ X17 ) )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('35',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['31','32','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_C = sk_B )
      | ( sk_C = sk_B ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C = sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('49',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['2','47','48'])).

thf('50',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('51',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('52',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('53',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('54',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('55',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X16 @ ( k2_tarski @ X14 @ X17 ) )
      | ( X16
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('57',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( X19 = X18 )
      | ( X19 = X20 )
      | ~ ( r1_tarski @ ( k1_tarski @ X19 ) @ ( k2_tarski @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('60',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('64',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('66',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('70',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('72',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('76',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = ( k1_tarski @ sk_A ) )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('79',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
    | ( sk_D = sk_C ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('85',plain,
    ( ( sk_C = sk_A )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('90',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X17 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('91',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = X2 )
      | ~ ( r1_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_tarski @ sk_C )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['49','87','88','89','92'])).

thf('94',plain,(
    ! [X14: $i,X17: $i] :
      ( r1_tarski @ ( k1_tarski @ X14 ) @ ( k2_tarski @ X14 @ X17 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('95',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('97',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wIVzMb2ySl
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:01:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 171 iterations in 0.080s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.38/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(t28_zfmisc_1, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.38/0.57          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.38/0.57             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(t28_xboole_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.57  thf('2', plain,
% 0.38/0.57      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.38/0.57         = (k2_tarski @ sk_A @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(l45_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.38/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.38/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.57         (((X16) = (k2_tarski @ X14 @ X15))
% 0.38/0.57          | ((X16) = (k1_tarski @ X15))
% 0.38/0.57          | ((X16) = (k1_tarski @ X14))
% 0.38/0.57          | ((X16) = (k1_xboole_0))
% 0.38/0.57          | ~ (r1_tarski @ X16 @ (k2_tarski @ X14 @ X15)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((r1_tarski @ X16 @ (k2_tarski @ X14 @ X17))
% 0.38/0.57          | ((X16) != (k1_tarski @ X14)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.38/0.57  thf('7', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (((r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['5', '7'])).
% 0.38/0.57  thf(t25_zfmisc_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.38/0.57          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.38/0.57  thf('9', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         (((X19) = (X18))
% 0.38/0.57          | ((X19) = (X20))
% 0.38/0.57          | ~ (r1_tarski @ (k1_tarski @ X19) @ (k2_tarski @ X18 @ X20)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((sk_C) = (sk_B))
% 0.38/0.57        | ((sk_C) = (sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain, (((sk_A) != (sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((sk_C) = (sk_B)))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.38/0.57        | ((sk_C) = (sk_B))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.57  thf(t69_enumset1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.38/0.57  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('16', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         (((X19) = (X18))
% 0.38/0.57          | ((X19) = (X20))
% 0.38/0.57          | ~ (r1_tarski @ (k1_tarski @ X19) @ (k2_tarski @ X18 @ X20)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.38/0.57          | ((X1) = (X0))
% 0.38/0.57          | ((X1) = (X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((sk_C) = (sk_B))
% 0.38/0.57        | ((sk_A) = (sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '18'])).
% 0.38/0.57  thf('20', plain, (((sk_A) != (sk_D))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((sk_C) = (sk_B)))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('23', plain,
% 0.38/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.38/0.57        | ((sk_C) = (sk_B))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((sk_C) = (sk_B))
% 0.38/0.57        | ((sk_A) = (sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.38/0.57  thf('26', plain, (((sk_A) != (sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('27', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.38/0.57           = (k1_tarski @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))
% 0.38/0.57        | ((sk_C) = (sk_B)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['27', '30'])).
% 0.38/0.57  thf(commutativity_k3_xboole_0, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('33', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('34', plain,
% 0.38/0.57      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((r1_tarski @ X16 @ (k2_tarski @ X14 @ X17))
% 0.38/0.57          | ((X16) != (k1_xboole_0)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.38/0.57  thf('35', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.57  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '35'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_C) = (sk_B)))),
% 0.38/0.57      inference('demod', [status(thm)], ['31', '32', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.38/0.57          | ((sk_C) = (sk_B))
% 0.38/0.57          | ((sk_A) = (X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.57  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '35'])).
% 0.38/0.57  thf('43', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('44', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X0) = (X1)) | ((sk_C) = (sk_B)) | ((sk_C) = (sk_B)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['43', '44'])).
% 0.38/0.57  thf('46', plain, (![X0 : $i, X1 : $i]: (((sk_C) = (sk_B)) | ((X0) = (X1)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.57  thf('47', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('48', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_C @ sk_D))
% 0.38/0.57         = (k2_tarski @ sk_A @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['2', '47', '48'])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.57  thf('51', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('52', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('53', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('54', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('55', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k2_tarski @ sk_C @ sk_D)))),
% 0.38/0.57      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.38/0.57  thf('56', plain,
% 0.38/0.57      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((r1_tarski @ X16 @ (k2_tarski @ X14 @ X17))
% 0.38/0.57          | ((X16) != (k1_tarski @ X17)))),
% 0.38/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X17) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      (((r1_tarski @ (k1_tarski @ sk_D) @ (k2_tarski @ sk_A @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['55', '57'])).
% 0.38/0.57  thf('59', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         (((X19) = (X18))
% 0.38/0.57          | ((X19) = (X20))
% 0.38/0.57          | ~ (r1_tarski @ (k1_tarski @ X19) @ (k2_tarski @ X18 @ X20)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.38/0.57  thf('60', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((sk_D) = (sk_C))
% 0.38/0.57        | ((sk_D) = (sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['58', '59'])).
% 0.38/0.57  thf('61', plain, (((sk_A) != (sk_D))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('62', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.38/0.57        | ((sk_D) = (sk_C)))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['60', '61'])).
% 0.38/0.57  thf('63', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('64', plain,
% 0.38/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.38/0.57        | ((sk_D) = (sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['62', '63'])).
% 0.38/0.57  thf('65', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('66', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((sk_D) = (sk_C))
% 0.38/0.57        | ((sk_A) = (sk_D)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['64', '65'])).
% 0.38/0.57  thf('67', plain, (((sk_A) != (sk_D))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('68', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.38/0.57        | ((sk_D) = (sk_C)))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.38/0.57  thf('69', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('70', plain,
% 0.38/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.38/0.57        | ((sk_D) = (sk_C))
% 0.38/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['68', '69'])).
% 0.38/0.57  thf('71', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('72', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.38/0.57        | ((sk_D) = (sk_C))
% 0.38/0.57        | ((sk_A) = (sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['70', '71'])).
% 0.38/0.57  thf('73', plain, (((sk_A) != (sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('74', plain,
% 0.38/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)) | ((sk_D) = (sk_C)))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.38/0.57  thf('75', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.38/0.57           = (k1_tarski @ X1))),
% 0.38/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.38/0.57  thf('76', plain,
% 0.38/0.57      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))
% 0.38/0.57        | ((sk_D) = (sk_C)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['74', '75'])).
% 0.38/0.57  thf('77', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('78', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.57  thf('79', plain,
% 0.38/0.57      ((((k1_xboole_0) = (k1_tarski @ sk_A)) | ((sk_D) = (sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.38/0.57  thf('80', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('81', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.38/0.57          | ((sk_D) = (sk_C))
% 0.38/0.57          | ((sk_A) = (X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['79', '80'])).
% 0.38/0.57  thf('82', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.38/0.57      inference('sup+', [status(thm)], ['33', '35'])).
% 0.38/0.57  thf('83', plain, (![X0 : $i]: (((sk_D) = (sk_C)) | ((sk_A) = (X0)))),
% 0.38/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.38/0.57  thf('84', plain, (((sk_C) = (sk_B))),
% 0.38/0.57      inference('condensation', [status(thm)], ['46'])).
% 0.38/0.57  thf('85', plain, ((((sk_C) = (sk_A)) | ((sk_D) = (sk_C)))),
% 0.38/0.57      inference('sup+', [status(thm)], ['83', '84'])).
% 0.38/0.57  thf('86', plain, (((sk_A) != (sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('87', plain, (((sk_D) = (sk_C))),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['85', '86'])).
% 0.38/0.57  thf('88', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.38/0.57  thf('89', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.38/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.38/0.57  thf('90', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X17) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.57  thf('91', plain,
% 0.38/0.57      (![X2 : $i, X3 : $i]:
% 0.38/0.57         (((k3_xboole_0 @ X2 @ X3) = (X2)) | ~ (r1_tarski @ X2 @ X3))),
% 0.38/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.38/0.57  thf('92', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.38/0.57           = (k1_tarski @ X0))),
% 0.38/0.57      inference('sup-', [status(thm)], ['90', '91'])).
% 0.38/0.57  thf('93', plain, (((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['49', '87', '88', '89', '92'])).
% 0.38/0.57  thf('94', plain,
% 0.38/0.57      (![X14 : $i, X17 : $i]:
% 0.38/0.57         (r1_tarski @ (k1_tarski @ X14) @ (k2_tarski @ X14 @ X17))),
% 0.38/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.57  thf('95', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.38/0.57      inference('sup+', [status(thm)], ['93', '94'])).
% 0.38/0.57  thf('96', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.38/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.38/0.57  thf('97', plain, (((sk_A) = (sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['95', '96'])).
% 0.38/0.57  thf('98', plain, (((sk_A) != (sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('99', plain, ($false),
% 0.38/0.57      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
