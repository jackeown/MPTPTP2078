%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DhNhbEX434

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  109 (2036 expanded)
%              Number of leaves         :   13 ( 565 expanded)
%              Depth                    :   39
%              Number of atoms          :  922 (22012 expanded)
%              Number of equality atoms :  156 (3644 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_C @ sk_D ) @ ( k2_tarski @ sk_A @ sk_B ) )
    | ( ( k2_tarski @ sk_C @ sk_D )
      = ( k2_tarski @ sk_A @ sk_B ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( X15
        = ( k2_tarski @ X13 @ X14 ) )
      | ( X15
        = ( k1_tarski @ X14 ) )
      | ( X15
        = ( k1_tarski @ X13 ) )
      | ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ ( k2_tarski @ X13 @ X14 ) ) ) ),
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
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ ( k2_tarski @ X13 @ X16 ) )
      | ( X15
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 = X17 )
      | ( X18 = X19 )
      | ~ ( r1_tarski @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X17 @ X19 ) ) ) ),
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
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
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
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 = X17 )
      | ( X18 = X19 )
      | ~ ( r1_tarski @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X17 @ X19 ) ) ) ),
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
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
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
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ ( k2_tarski @ X13 @ X16 ) )
      | ( X15 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('32',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_C = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_C = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_C = sk_B )
      | ( sk_C = sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_C = sk_B )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('45',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_C @ sk_D ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_C @ sk_D )
      = ( k2_tarski @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','44','45'])).

thf('47',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('48',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('49',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('50',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('51',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('52',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ ( k2_tarski @ X13 @ X16 ) )
      | ( X15
       != ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('54',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 = X17 )
      | ( X18 = X19 )
      | ~ ( r1_tarski @ ( k1_tarski @ X18 ) @ ( k2_tarski @ X17 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('57',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('61',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('63',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('67',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('69',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('73',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('75',plain,
    ( ( sk_D = sk_C )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['43'])).

thf('81',plain,
    ( ( sk_C = sk_A )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('85',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X16 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('86',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf('87',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('88',plain,
    ( ( k1_tarski @ sk_C )
    = ( k2_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['46','83','84','85','86','87'])).

thf('89',plain,(
    ! [X13: $i,X16: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X13 @ X16 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('90',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('92',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DhNhbEX434
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:15:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.57  % Solved by: fo/fo7.sh
% 0.22/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.57  % done 157 iterations in 0.104s
% 0.22/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.57  % SZS output start Refutation
% 0.22/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.57  thf(t28_zfmisc_1, conjecture,
% 0.22/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.57     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.22/0.57          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.22/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.57        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.22/0.57             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.22/0.57    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.22/0.57  thf('0', plain,
% 0.22/0.57      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(d10_xboole_0, axiom,
% 0.22/0.57    (![A:$i,B:$i]:
% 0.22/0.57     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.57  thf('1', plain,
% 0.22/0.57      (![X0 : $i, X2 : $i]:
% 0.22/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('2', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k2_tarski @ sk_C @ sk_D) @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.57        | ((k2_tarski @ sk_C @ sk_D) = (k2_tarski @ sk_A @ sk_B)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.57  thf('3', plain,
% 0.22/0.57      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf(l45_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.22/0.57       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.22/0.57            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.22/0.57  thf('4', plain,
% 0.22/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.57         (((X15) = (k2_tarski @ X13 @ X14))
% 0.22/0.57          | ((X15) = (k1_tarski @ X14))
% 0.22/0.57          | ((X15) = (k1_tarski @ X13))
% 0.22/0.57          | ((X15) = (k1_xboole_0))
% 0.22/0.57          | ~ (r1_tarski @ X15 @ (k2_tarski @ X13 @ X14)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.57  thf('5', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf('6', plain,
% 0.22/0.57      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         ((r1_tarski @ X15 @ (k2_tarski @ X13 @ X16))
% 0.22/0.57          | ((X15) != (k1_tarski @ X13)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.57  thf('7', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('8', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['5', '7'])).
% 0.22/0.57  thf(t25_zfmisc_1, axiom,
% 0.22/0.57    (![A:$i,B:$i,C:$i]:
% 0.22/0.57     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.22/0.57          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.57  thf('9', plain,
% 0.22/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.57         (((X18) = (X17))
% 0.22/0.57          | ((X18) = (X19))
% 0.22/0.57          | ~ (r1_tarski @ (k1_tarski @ X18) @ (k2_tarski @ X17 @ X19)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.22/0.57  thf('10', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((sk_C) = (sk_B))
% 0.22/0.57        | ((sk_C) = (sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.57  thf('11', plain, (((sk_A) != (sk_C))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('12', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((sk_C) = (sk_B)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.22/0.57  thf('13', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('14', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.22/0.57        | ((sk_C) = (sk_B))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.57  thf(t69_enumset1, axiom,
% 0.22/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.57  thf('15', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.57  thf('16', plain,
% 0.22/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.57         (((X18) = (X17))
% 0.22/0.57          | ((X18) = (X19))
% 0.22/0.57          | ~ (r1_tarski @ (k1_tarski @ X18) @ (k2_tarski @ X17 @ X19)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.22/0.57  thf('17', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.22/0.57          | ((X1) = (X0))
% 0.22/0.57          | ((X1) = (X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.57  thf('18', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('19', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((sk_C) = (sk_B))
% 0.22/0.57        | ((sk_A) = (sk_D)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['14', '18'])).
% 0.22/0.57  thf('20', plain, (((sk_A) != (sk_D))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('21', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((sk_C) = (sk_B)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.22/0.57  thf('22', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('23', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.22/0.57        | ((sk_C) = (sk_B))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.57  thf('24', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('25', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((sk_C) = (sk_B))
% 0.22/0.57        | ((sk_A) = (sk_C)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.57  thf('26', plain, (((sk_A) != (sk_C))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('27', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.22/0.57  thf('28', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('29', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_C) = (sk_B)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['27', '28'])).
% 0.22/0.57  thf('30', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.57  thf('31', plain,
% 0.22/0.57      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         ((r1_tarski @ X15 @ (k2_tarski @ X13 @ X16))
% 0.22/0.57          | ((X15) != (k1_xboole_0)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.57  thf('32', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['31'])).
% 0.22/0.57  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['30', '32'])).
% 0.22/0.57  thf('34', plain,
% 0.22/0.57      (![X0 : $i, X2 : $i]:
% 0.22/0.57         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.57      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.57  thf('35', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.22/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('36', plain,
% 0.22/0.57      ((((sk_C) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['29', '35'])).
% 0.22/0.57  thf('37', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('38', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.57          | ((sk_C) = (sk_B))
% 0.22/0.57          | ((sk_A) = (X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.57  thf('39', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['30', '32'])).
% 0.22/0.57  thf('40', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf('41', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['38', '39'])).
% 0.22/0.57  thf('42', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X0) = (X1)) | ((sk_C) = (sk_B)) | ((sk_C) = (sk_B)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['40', '41'])).
% 0.22/0.57  thf('43', plain, (![X0 : $i, X1 : $i]: (((sk_C) = (sk_B)) | ((X0) = (X1)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.57  thf('44', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('45', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('46', plain,
% 0.22/0.57      ((~ (r1_tarski @ (k2_tarski @ sk_C @ sk_D) @ (k2_tarski @ sk_A @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_C @ sk_D) = (k2_tarski @ sk_A @ sk_C)))),
% 0.22/0.57      inference('demod', [status(thm)], ['2', '44', '45'])).
% 0.22/0.57  thf('47', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.57  thf('48', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('49', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('50', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('51', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('52', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k2_tarski @ sk_C @ sk_D)))),
% 0.22/0.57      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.22/0.57  thf('53', plain,
% 0.22/0.57      (![X13 : $i, X15 : $i, X16 : $i]:
% 0.22/0.57         ((r1_tarski @ X15 @ (k2_tarski @ X13 @ X16))
% 0.22/0.57          | ((X15) != (k1_tarski @ X16)))),
% 0.22/0.57      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.22/0.57  thf('54', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X16) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.57  thf('55', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_D) @ (k2_tarski @ sk_A @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['52', '54'])).
% 0.22/0.57  thf('56', plain,
% 0.22/0.57      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.57         (((X18) = (X17))
% 0.22/0.57          | ((X18) = (X19))
% 0.22/0.57          | ~ (r1_tarski @ (k1_tarski @ X18) @ (k2_tarski @ X17 @ X19)))),
% 0.22/0.57      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.22/0.57  thf('57', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((sk_D) = (sk_C))
% 0.22/0.57        | ((sk_D) = (sk_A)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.57  thf('58', plain, (((sk_A) != (sk_D))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('59', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.22/0.57        | ((sk_D) = (sk_C)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.22/0.57  thf('60', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('61', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.22/0.57        | ((sk_D) = (sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['59', '60'])).
% 0.22/0.57  thf('62', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('63', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((sk_D) = (sk_C))
% 0.22/0.57        | ((sk_A) = (sk_D)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.57  thf('64', plain, (((sk_A) != (sk_D))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('65', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.22/0.57        | ((sk_D) = (sk_C)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.22/0.57  thf('66', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('67', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.22/0.57        | ((sk_D) = (sk_C))
% 0.22/0.57        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['65', '66'])).
% 0.22/0.57  thf('68', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('69', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.22/0.57        | ((sk_D) = (sk_C))
% 0.22/0.57        | ((sk_A) = (sk_C)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['67', '68'])).
% 0.22/0.57  thf('70', plain, (((sk_A) != (sk_C))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('71', plain,
% 0.22/0.57      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)) | ((sk_D) = (sk_C)))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['69', '70'])).
% 0.22/0.57  thf('72', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('73', plain,
% 0.22/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_D) = (sk_C)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['71', '72'])).
% 0.22/0.57  thf('74', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r1_tarski @ (k1_tarski @ X0) @ k1_xboole_0)
% 0.22/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.57  thf('75', plain,
% 0.22/0.57      ((((sk_D) = (sk_C)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['73', '74'])).
% 0.22/0.57  thf('76', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('77', plain,
% 0.22/0.57      (![X0 : $i]:
% 0.22/0.57         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.22/0.57          | ((sk_D) = (sk_C))
% 0.22/0.57          | ((sk_A) = (X0)))),
% 0.22/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.22/0.57  thf('78', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.22/0.57      inference('sup+', [status(thm)], ['30', '32'])).
% 0.22/0.57  thf('79', plain, (![X0 : $i]: (((sk_D) = (sk_C)) | ((sk_A) = (X0)))),
% 0.22/0.57      inference('demod', [status(thm)], ['77', '78'])).
% 0.22/0.57  thf('80', plain, (((sk_C) = (sk_B))),
% 0.22/0.57      inference('condensation', [status(thm)], ['43'])).
% 0.22/0.57  thf('81', plain, ((((sk_C) = (sk_A)) | ((sk_D) = (sk_C)))),
% 0.22/0.57      inference('sup+', [status(thm)], ['79', '80'])).
% 0.22/0.57  thf('82', plain, (((sk_A) != (sk_C))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('83', plain, (((sk_D) = (sk_C))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.22/0.57  thf('84', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.57  thf('85', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X16) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.57  thf('86', plain, (((sk_D) = (sk_C))),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 0.22/0.57  thf('87', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.22/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.57  thf('88', plain, (((k1_tarski @ sk_C) = (k2_tarski @ sk_A @ sk_C))),
% 0.22/0.57      inference('demod', [status(thm)], ['46', '83', '84', '85', '86', '87'])).
% 0.22/0.57  thf('89', plain,
% 0.22/0.57      (![X13 : $i, X16 : $i]:
% 0.22/0.57         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X13 @ X16))),
% 0.22/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.57  thf('90', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.22/0.57      inference('sup+', [status(thm)], ['88', '89'])).
% 0.22/0.57  thf('91', plain,
% 0.22/0.57      (![X0 : $i, X1 : $i]:
% 0.22/0.57         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.22/0.57      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.57  thf('92', plain, (((sk_A) = (sk_C))),
% 0.22/0.57      inference('sup-', [status(thm)], ['90', '91'])).
% 0.22/0.57  thf('93', plain, (((sk_A) != (sk_C))),
% 0.22/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.57  thf('94', plain, ($false),
% 0.22/0.57      inference('simplify_reflect-', [status(thm)], ['92', '93'])).
% 0.22/0.57  
% 0.22/0.57  % SZS output end Refutation
% 0.22/0.57  
% 0.22/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
