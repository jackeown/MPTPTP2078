%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gA0egGbyCZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 (2009 expanded)
%              Number of leaves         :   15 ( 574 expanded)
%              Depth                    :   41
%              Number of atoms          :  988 (21244 expanded)
%              Number of equality atoms :  167 (3517 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( X12
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12
        = ( k1_tarski @ X10 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X11 ) ) ) ),
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
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X13 ) )
      | ( X12
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('7',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 = X14 )
      | ( X15 = X16 )
      | ~ ( r1_tarski @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X14 @ X16 ) ) ) ),
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
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 = X14 )
      | ( X15 = X16 )
      | ~ ( r1_tarski @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X14 @ X16 ) ) ) ),
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
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
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
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('29',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_C = sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,
    ( ( sk_C = sk_B )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('33',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X13 ) )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('35',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_C = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
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

thf('48',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ ( k2_tarski @ sk_C @ sk_D ) )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['2','47'])).

thf('49',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_B )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('50',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('51',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('52',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('53',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('54',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k2_tarski @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k2_tarski @ X10 @ X13 ) )
      | ( X12
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('56',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_D ) @ ( k2_tarski @ sk_A @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','56'])).

thf('58',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( X15 = X14 )
      | ( X15 = X16 )
      | ~ ( r1_tarski @ ( k1_tarski @ X15 ) @ ( k2_tarski @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t25_zfmisc_1])).

thf('59',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( sk_D = sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('63',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_D ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('65',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( sk_A = sk_D ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('69',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_C )
    | ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('71',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( ( k2_tarski @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('75',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('77',plain,
    ( ( sk_D = sk_C )
    | ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('80',plain,
    ( ( sk_D = sk_C )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','35'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( sk_D = sk_C )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    sk_C = sk_B ),
    inference(condensation,[status(thm)],['46'])).

thf('86',plain,
    ( ( sk_C = sk_A )
    | ( sk_D = sk_C ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('91',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('92',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    sk_D = sk_C ),
    inference('simplify_reflect-',[status(thm)],['86','87'])).

thf('95',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('96',plain,
    ( ( k2_tarski @ sk_A @ sk_C )
    = ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['48','88','89','90','93','94','95'])).

thf('97',plain,(
    ! [X10: $i,X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k2_tarski @ X10 @ X13 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('98',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('sup+',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('100',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gA0egGbyCZ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 157 iterations in 0.104s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(t28_zfmisc_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.56          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.21/0.56             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t12_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))
% 0.21/0.56         = (k2_tarski @ sk_C @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(l45_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.56       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.56            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         (((X12) = (k2_tarski @ X10 @ X11))
% 0.21/0.56          | ((X12) = (k1_tarski @ X11))
% 0.21/0.56          | ((X12) = (k1_tarski @ X10))
% 0.21/0.56          | ((X12) = (k1_xboole_0))
% 0.21/0.56          | ~ (r1_tarski @ X12 @ (k2_tarski @ X10 @ X11)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         ((r1_tarski @ X12 @ (k2_tarski @ X10 @ X13))
% 0.21/0.56          | ((X12) != (k1_tarski @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_C) @ (k2_tarski @ sk_A @ sk_B))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['5', '7'])).
% 0.21/0.56  thf(t25_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.21/0.56          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (((X15) = (X14))
% 0.21/0.56          | ((X15) = (X16))
% 0.21/0.56          | ~ (r1_tarski @ (k1_tarski @ X15) @ (k2_tarski @ X14 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((sk_C) = (sk_B))
% 0.21/0.56        | ((sk_C) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain, (((sk_A) != (sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((sk_C) = (sk_B)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.21/0.56        | ((sk_C) = (sk_B))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf(t69_enumset1, axiom,
% 0.21/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.56  thf('15', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (((X15) = (X14))
% 0.21/0.56          | ((X15) = (X16))
% 0.21/0.56          | ~ (r1_tarski @ (k1_tarski @ X15) @ (k2_tarski @ X14 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.21/0.56          | ((X1) = (X0))
% 0.21/0.56          | ((X1) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((sk_C) = (sk_B))
% 0.21/0.56        | ((sk_A) = (sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.56  thf('20', plain, (((sk_A) != (sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((sk_C) = (sk_B)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.21/0.56        | ((sk_C) = (sk_B))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((sk_C) = (sk_B))
% 0.21/0.56        | ((sk_A) = (sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.56  thf('26', plain, (((sk_A) != (sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0)) | ((sk_C) = (sk_B)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('29', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_C) = (sk_B)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['27', '28'])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((sk_C) = (sk_B))
% 0.21/0.56        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.56  thf('33', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         ((r1_tarski @ X12 @ (k2_tarski @ X10 @ X13))
% 0.21/0.56          | ((X12) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ k1_xboole_0 @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.56  thf('36', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('38', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      ((((sk_C) = (sk_B)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32', '38'])).
% 0.21/0.56  thf('40', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56          | ((sk_C) = (sk_B))
% 0.21/0.56          | ((sk_A) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '35'])).
% 0.21/0.56  thf('43', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('44', plain, (![X0 : $i]: (((sk_C) = (sk_B)) | ((sk_A) = (X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (X1)) | ((sk_C) = (sk_B)) | ((sk_C) = (sk_B)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['43', '44'])).
% 0.21/0.56  thf('46', plain, (![X0 : $i, X1 : $i]: (((sk_C) = (sk_B)) | ((X0) = (X1)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.56  thf('47', plain, (((sk_C) = (sk_B))),
% 0.21/0.56      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.56  thf('48', plain,
% 0.21/0.56      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ (k2_tarski @ sk_C @ sk_D))
% 0.21/0.56         = (k2_tarski @ sk_C @ sk_D))),
% 0.21/0.56      inference('demod', [status(thm)], ['2', '47'])).
% 0.21/0.56  thf('49', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_B) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.56  thf('50', plain, (((sk_C) = (sk_B))),
% 0.21/0.56      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.56  thf('51', plain, (((sk_C) = (sk_B))),
% 0.21/0.56      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.56  thf('52', plain, (((sk_C) = (sk_B))),
% 0.21/0.56      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.56  thf('53', plain, (((sk_C) = (sk_B))),
% 0.21/0.56      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k2_tarski @ sk_C @ sk_D)))),
% 0.21/0.56      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.56         ((r1_tarski @ X12 @ (k2_tarski @ X10 @ X13))
% 0.21/0.56          | ((X12) != (k1_tarski @ X13)))),
% 0.21/0.56      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.56  thf('56', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.56  thf('57', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_D) @ (k2_tarski @ sk_A @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['54', '56'])).
% 0.21/0.56  thf('58', plain,
% 0.21/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.56         (((X15) = (X14))
% 0.21/0.56          | ((X15) = (X16))
% 0.21/0.56          | ~ (r1_tarski @ (k1_tarski @ X15) @ (k2_tarski @ X14 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t25_zfmisc_1])).
% 0.21/0.56  thf('59', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((sk_D) = (sk_C))
% 0.21/0.56        | ((sk_D) = (sk_A)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.56  thf('60', plain, (((sk_A) != (sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('61', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_D))
% 0.21/0.56        | ((sk_D) = (sk_C)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['59', '60'])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_D))
% 0.21/0.56        | ((sk_D) = (sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['61', '62'])).
% 0.21/0.56  thf('64', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((sk_D) = (sk_C))
% 0.21/0.56        | ((sk_A) = (sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.56  thf('66', plain, (((sk_A) != (sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('67', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))
% 0.21/0.56        | ((sk_D) = (sk_C)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['65', '66'])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('69', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.21/0.56        | ((sk_D) = (sk_C))
% 0.21/0.56        | ((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('71', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.56        | ((sk_D) = (sk_C))
% 0.21/0.56        | ((sk_A) = (sk_C)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.56  thf('72', plain, (((sk_A) != (sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      ((((k2_tarski @ sk_A @ sk_C) = (k1_xboole_0)) | ((sk_D) = (sk_C)))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['71', '72'])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      (((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0) | ((sk_D) = (sk_C)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['73', '74'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('77', plain,
% 0.21/0.56      ((((sk_D) = (sk_C))
% 0.21/0.56        | ((k2_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['75', '76'])).
% 0.21/0.56  thf('78', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.56  thf('79', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_tarski @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('80', plain,
% 0.21/0.56      ((((sk_D) = (sk_C)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.21/0.56  thf('81', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('82', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))
% 0.21/0.56          | ((sk_D) = (sk_C))
% 0.21/0.56          | ((sk_A) = (X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.21/0.56  thf('83', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['33', '35'])).
% 0.21/0.56  thf('84', plain, (![X0 : $i]: (((sk_D) = (sk_C)) | ((sk_A) = (X0)))),
% 0.21/0.56      inference('demod', [status(thm)], ['82', '83'])).
% 0.21/0.56  thf('85', plain, (((sk_C) = (sk_B))),
% 0.21/0.56      inference('condensation', [status(thm)], ['46'])).
% 0.21/0.56  thf('86', plain, ((((sk_C) = (sk_A)) | ((sk_D) = (sk_C)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['84', '85'])).
% 0.21/0.56  thf('87', plain, (((sk_A) != (sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('88', plain, (((sk_D) = (sk_C))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf('89', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('90', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.56  thf('91', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X13) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['55'])).
% 0.21/0.56  thf('92', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.21/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.56  thf('93', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.21/0.56           = (k2_tarski @ X1 @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['91', '92'])).
% 0.21/0.56  thf('94', plain, (((sk_D) = (sk_C))),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['86', '87'])).
% 0.21/0.56  thf('95', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.21/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.56  thf('96', plain, (((k2_tarski @ sk_A @ sk_C) = (k1_tarski @ sk_C))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['48', '88', '89', '90', '93', '94', '95'])).
% 0.21/0.56  thf('97', plain,
% 0.21/0.56      (![X10 : $i, X13 : $i]:
% 0.21/0.56         (r1_tarski @ (k1_tarski @ X10) @ (k2_tarski @ X10 @ X13))),
% 0.21/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.56  thf('98', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.21/0.56      inference('sup+', [status(thm)], ['96', '97'])).
% 0.21/0.56  thf('99', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X1) = (X0)) | ~ (r1_tarski @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf('100', plain, (((sk_A) = (sk_C))),
% 0.21/0.56      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.56  thf('101', plain, (((sk_A) != (sk_C))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('102', plain, ($false),
% 0.21/0.56      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
