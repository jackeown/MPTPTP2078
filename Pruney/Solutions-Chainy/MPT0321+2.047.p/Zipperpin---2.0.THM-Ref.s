%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X9lCf4FITV

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:39 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 335 expanded)
%              Number of leaves         :   14 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          :  759 (3921 expanded)
%              Number of equality atoms :   86 ( 571 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ X1 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

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

thf('5',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( X0 = sk_C_1 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ sk_C_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['14','15','16'])).

thf('18',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_C_1 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('28',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_D = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('30',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_A ) @ sk_A )
    | ( sk_A = sk_C_1 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('33',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( ( sk_C_1 != sk_C_1 )
      | ( sk_D = k1_xboole_0 ) )
   <= ( sk_A != sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A != sk_C_1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['14','15','16'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('41',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['14','15','16'])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('44',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ X1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) )
      | ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ X0 )
      | ( X0 = sk_D )
      | ( r2_hidden @ ( sk_C @ sk_D @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_D ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X7 ) )
      | ~ ( r2_hidden @ X5 @ X7 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B_1 = sk_D )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = sk_D ) ),
    inference('sup-',[status(thm)],['41','53'])).

thf('55',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ sk_D @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( sk_B_1 = sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('58',plain,
    ( ( sk_B_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('60',plain,
    ( ( sk_B_1 = sk_D )
    | ~ ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_D ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_B_1 ) @ sk_B_1 )
    | ( sk_B_1 = sk_D ) ),
    inference(eq_fact,[status(thm)],['50'])).

thf('63',plain,(
    sk_B_1 = sk_D ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['38','63'])).

thf('65',plain,
    ( $false
   <= ( sk_A != sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','64'])).

thf('66',plain,(
    sk_B_1 = sk_D ),
    inference(clc,[status(thm)],['61','62'])).

thf('67',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('68',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_B_1 = sk_D ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['34'])).

thf('71',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['65','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.X9lCf4FITV
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.73/2.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.73/2.99  % Solved by: fo/fo7.sh
% 2.73/2.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.73/2.99  % done 744 iterations in 2.531s
% 2.73/2.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.73/2.99  % SZS output start Refutation
% 2.73/2.99  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.73/2.99  thf(sk_A_type, type, sk_A: $i).
% 2.73/2.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.73/2.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.73/2.99  thf(sk_D_type, type, sk_D: $i).
% 2.73/2.99  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.73/2.99  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.73/2.99  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.73/2.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 2.73/2.99  thf(sk_B_type, type, sk_B: $i > $i).
% 2.73/2.99  thf(t2_tarski, axiom,
% 2.73/2.99    (![A:$i,B:$i]:
% 2.73/2.99     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 2.73/2.99       ( ( A ) = ( B ) ) ))).
% 2.73/2.99  thf('0', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (((X1) = (X0))
% 2.73/2.99          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 2.73/2.99          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.73/2.99      inference('cnf', [status(esa)], [t2_tarski])).
% 2.73/2.99  thf(t7_xboole_0, axiom,
% 2.73/2.99    (![A:$i]:
% 2.73/2.99     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.73/2.99          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.73/2.99  thf('1', plain,
% 2.73/2.99      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.73/2.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.73/2.99  thf(l54_zfmisc_1, axiom,
% 2.73/2.99    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.99     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 2.73/2.99       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 2.73/2.99  thf('2', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 2.73/2.99         ((r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X7))
% 2.73/2.99          | ~ (r2_hidden @ X5 @ X7)
% 2.73/2.99          | ~ (r2_hidden @ X3 @ X4))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('3', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         (((X0) = (k1_xboole_0))
% 2.73/2.99          | ~ (r2_hidden @ X2 @ X1)
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X1 @ X0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['1', '2'])).
% 2.73/2.99  thf('4', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 2.73/2.99          | ((X1) = (X0))
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ (sk_C @ X0 @ X1) @ (sk_B @ X2)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X0 @ X2))
% 2.73/2.99          | ((X2) = (k1_xboole_0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['0', '3'])).
% 2.73/2.99  thf(t134_zfmisc_1, conjecture,
% 2.73/2.99    (![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.99     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.73/2.99       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.99         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 2.73/2.99  thf(zf_stmt_0, negated_conjecture,
% 2.73/2.99    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.73/2.99        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 2.73/2.99          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 2.73/2.99            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 2.73/2.99    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 2.73/2.99  thf('5', plain,
% 2.73/2.99      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('6', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.73/2.99         ((r2_hidden @ X3 @ X4)
% 2.73/2.99          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('7', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 2.73/2.99          | (r2_hidden @ X1 @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['5', '6'])).
% 2.73/2.99  thf('8', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         (((sk_D) = (k1_xboole_0))
% 2.73/2.99          | ((X0) = (sk_C_1))
% 2.73/2.99          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ X0)
% 2.73/2.99          | (r2_hidden @ (sk_C @ sk_C_1 @ X0) @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['4', '7'])).
% 2.73/2.99  thf('9', plain,
% 2.73/2.99      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_A) @ sk_A)
% 2.73/2.99        | ((sk_A) = (sk_C_1))
% 2.73/2.99        | ((sk_D) = (k1_xboole_0)))),
% 2.73/2.99      inference('eq_fact', [status(thm)], ['8'])).
% 2.73/2.99  thf('10', plain,
% 2.73/2.99      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('11', plain,
% 2.73/2.99      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 2.73/2.99      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.73/2.99  thf('12', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.73/2.99         (((X0) = (k1_xboole_0))
% 2.73/2.99          | ~ (r2_hidden @ X2 @ X1)
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X1 @ X0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['1', '2'])).
% 2.73/2.99  thf('13', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (((X0) = (k1_xboole_0))
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X0 @ X1))
% 2.73/2.99          | ((X1) = (k1_xboole_0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['11', '12'])).
% 2.73/2.99  thf('14', plain,
% 2.73/2.99      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99         (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 2.73/2.99        | ((sk_B_1) = (k1_xboole_0))
% 2.73/2.99        | ((sk_A) = (k1_xboole_0)))),
% 2.73/2.99      inference('sup+', [status(thm)], ['10', '13'])).
% 2.73/2.99  thf('15', plain, (((sk_A) != (k1_xboole_0))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('16', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('17', plain,
% 2.73/2.99      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('simplify_reflect-', [status(thm)], ['14', '15', '16'])).
% 2.73/2.99  thf('18', plain,
% 2.73/2.99      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('19', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.73/2.99         ((r2_hidden @ X5 @ X6)
% 2.73/2.99          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('20', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 2.73/2.99          | (r2_hidden @ X0 @ sk_B_1))),
% 2.73/2.99      inference('sup-', [status(thm)], ['18', '19'])).
% 2.73/2.99  thf('21', plain, ((r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 2.73/2.99      inference('sup-', [status(thm)], ['17', '20'])).
% 2.73/2.99  thf('22', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 2.73/2.99         ((r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X7))
% 2.73/2.99          | ~ (r2_hidden @ X5 @ X7)
% 2.73/2.99          | ~ (r2_hidden @ X3 @ X4))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('23', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (~ (r2_hidden @ X1 @ X0)
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ X1 @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['21', '22'])).
% 2.73/2.99  thf('24', plain,
% 2.73/2.99      ((((sk_D) = (k1_xboole_0))
% 2.73/2.99        | ((sk_A) = (sk_C_1))
% 2.73/2.99        | (r2_hidden @ 
% 2.73/2.99           (k4_tarski @ (sk_C @ sk_C_1 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99           (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['9', '23'])).
% 2.73/2.99  thf('25', plain,
% 2.73/2.99      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('26', plain,
% 2.73/2.99      ((((sk_D) = (k1_xboole_0))
% 2.73/2.99        | ((sk_A) = (sk_C_1))
% 2.73/2.99        | (r2_hidden @ 
% 2.73/2.99           (k4_tarski @ (sk_C @ sk_C_1 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99           (k2_zfmisc_1 @ sk_C_1 @ sk_D)))),
% 2.73/2.99      inference('demod', [status(thm)], ['24', '25'])).
% 2.73/2.99  thf('27', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.73/2.99         ((r2_hidden @ X3 @ X4)
% 2.73/2.99          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('28', plain,
% 2.73/2.99      ((((sk_A) = (sk_C_1))
% 2.73/2.99        | ((sk_D) = (k1_xboole_0))
% 2.73/2.99        | (r2_hidden @ (sk_C @ sk_C_1 @ sk_A) @ sk_C_1))),
% 2.73/2.99      inference('sup-', [status(thm)], ['26', '27'])).
% 2.73/2.99  thf('29', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (((X1) = (X0))
% 2.73/2.99          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 2.73/2.99          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.73/2.99      inference('cnf', [status(esa)], [t2_tarski])).
% 2.73/2.99  thf('30', plain,
% 2.73/2.99      ((((sk_D) = (k1_xboole_0))
% 2.73/2.99        | ((sk_A) = (sk_C_1))
% 2.73/2.99        | ~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_A) @ sk_A)
% 2.73/2.99        | ((sk_A) = (sk_C_1)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['28', '29'])).
% 2.73/2.99  thf('31', plain,
% 2.73/2.99      ((~ (r2_hidden @ (sk_C @ sk_C_1 @ sk_A) @ sk_A)
% 2.73/2.99        | ((sk_A) = (sk_C_1))
% 2.73/2.99        | ((sk_D) = (k1_xboole_0)))),
% 2.73/2.99      inference('simplify', [status(thm)], ['30'])).
% 2.73/2.99  thf('32', plain,
% 2.73/2.99      (((r2_hidden @ (sk_C @ sk_C_1 @ sk_A) @ sk_A)
% 2.73/2.99        | ((sk_A) = (sk_C_1))
% 2.73/2.99        | ((sk_D) = (k1_xboole_0)))),
% 2.73/2.99      inference('eq_fact', [status(thm)], ['8'])).
% 2.73/2.99  thf('33', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 2.73/2.99      inference('clc', [status(thm)], ['31', '32'])).
% 2.73/2.99  thf('34', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) != (sk_D)))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('35', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 2.73/2.99      inference('split', [status(esa)], ['34'])).
% 2.73/2.99  thf('36', plain,
% 2.73/2.99      (((((sk_C_1) != (sk_C_1)) | ((sk_D) = (k1_xboole_0))))
% 2.73/2.99         <= (~ (((sk_A) = (sk_C_1))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['33', '35'])).
% 2.73/2.99  thf('37', plain, ((((sk_D) = (k1_xboole_0))) <= (~ (((sk_A) = (sk_C_1))))),
% 2.73/2.99      inference('simplify', [status(thm)], ['36'])).
% 2.73/2.99  thf('38', plain, (((sk_B_1) != (k1_xboole_0))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('39', plain,
% 2.73/2.99      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('simplify_reflect-', [status(thm)], ['14', '15', '16'])).
% 2.73/2.99  thf('40', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 2.73/2.99          | (r2_hidden @ X1 @ sk_A))),
% 2.73/2.99      inference('sup-', [status(thm)], ['5', '6'])).
% 2.73/2.99  thf('41', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_A)),
% 2.73/2.99      inference('sup-', [status(thm)], ['39', '40'])).
% 2.73/2.99  thf('42', plain,
% 2.73/2.99      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 2.73/2.99        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('simplify_reflect-', [status(thm)], ['14', '15', '16'])).
% 2.73/2.99  thf('43', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.73/2.99         ((r2_hidden @ X3 @ X4)
% 2.73/2.99          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('44', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_C_1)),
% 2.73/2.99      inference('sup-', [status(thm)], ['42', '43'])).
% 2.73/2.99  thf('45', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (((X1) = (X0))
% 2.73/2.99          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 2.73/2.99          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.73/2.99      inference('cnf', [status(esa)], [t2_tarski])).
% 2.73/2.99  thf('46', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 2.73/2.99         ((r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X7))
% 2.73/2.99          | ~ (r2_hidden @ X5 @ X7)
% 2.73/2.99          | ~ (r2_hidden @ X3 @ X4))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('47', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.73/2.99         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 2.73/2.99          | ((X1) = (X0))
% 2.73/2.99          | ~ (r2_hidden @ X3 @ X2)
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X0 @ X1)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X2 @ X0)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['45', '46'])).
% 2.73/2.99  thf('48', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ X1)) @ 
% 2.73/2.99           (k2_zfmisc_1 @ sk_C_1 @ X0))
% 2.73/2.99          | ((X1) = (X0))
% 2.73/2.99          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.73/2.99      inference('sup-', [status(thm)], ['44', '47'])).
% 2.73/2.99  thf('49', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 2.73/2.99          | (r2_hidden @ X0 @ sk_B_1))),
% 2.73/2.99      inference('sup-', [status(thm)], ['18', '19'])).
% 2.73/2.99  thf('50', plain,
% 2.73/2.99      (![X0 : $i]:
% 2.73/2.99         ((r2_hidden @ (sk_C @ sk_D @ X0) @ X0)
% 2.73/2.99          | ((X0) = (sk_D))
% 2.73/2.99          | (r2_hidden @ (sk_C @ sk_D @ X0) @ sk_B_1))),
% 2.73/2.99      inference('sup-', [status(thm)], ['48', '49'])).
% 2.73/2.99  thf('51', plain,
% 2.73/2.99      (((r2_hidden @ (sk_C @ sk_D @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('eq_fact', [status(thm)], ['50'])).
% 2.73/2.99  thf('52', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X7 : $i]:
% 2.73/2.99         ((r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X7))
% 2.73/2.99          | ~ (r2_hidden @ X5 @ X7)
% 2.73/2.99          | ~ (r2_hidden @ X3 @ X4))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('53', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (((sk_B_1) = (sk_D))
% 2.73/2.99          | ~ (r2_hidden @ X1 @ X0)
% 2.73/2.99          | (r2_hidden @ (k4_tarski @ X1 @ (sk_C @ sk_D @ sk_B_1)) @ 
% 2.73/2.99             (k2_zfmisc_1 @ X0 @ sk_B_1)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['51', '52'])).
% 2.73/2.99  thf('54', plain,
% 2.73/2.99      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ sk_D @ sk_B_1)) @ 
% 2.73/2.99         (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.73/2.99        | ((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['41', '53'])).
% 2.73/2.99  thf('55', plain,
% 2.73/2.99      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 2.73/2.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.73/2.99  thf('56', plain,
% 2.73/2.99      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ sk_D @ sk_B_1)) @ 
% 2.73/2.99         (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 2.73/2.99        | ((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('demod', [status(thm)], ['54', '55'])).
% 2.73/2.99  thf('57', plain,
% 2.73/2.99      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.73/2.99         ((r2_hidden @ X5 @ X6)
% 2.73/2.99          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X6)))),
% 2.73/2.99      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 2.73/2.99  thf('58', plain,
% 2.73/2.99      ((((sk_B_1) = (sk_D)) | (r2_hidden @ (sk_C @ sk_D @ sk_B_1) @ sk_D))),
% 2.73/2.99      inference('sup-', [status(thm)], ['56', '57'])).
% 2.73/2.99  thf('59', plain,
% 2.73/2.99      (![X0 : $i, X1 : $i]:
% 2.73/2.99         (((X1) = (X0))
% 2.73/2.99          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 2.73/2.99          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.73/2.99      inference('cnf', [status(esa)], [t2_tarski])).
% 2.73/2.99  thf('60', plain,
% 2.73/2.99      ((((sk_B_1) = (sk_D))
% 2.73/2.99        | ~ (r2_hidden @ (sk_C @ sk_D @ sk_B_1) @ sk_B_1)
% 2.73/2.99        | ((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('sup-', [status(thm)], ['58', '59'])).
% 2.73/2.99  thf('61', plain,
% 2.73/2.99      ((~ (r2_hidden @ (sk_C @ sk_D @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('simplify', [status(thm)], ['60'])).
% 2.73/2.99  thf('62', plain,
% 2.73/2.99      (((r2_hidden @ (sk_C @ sk_D @ sk_B_1) @ sk_B_1) | ((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('eq_fact', [status(thm)], ['50'])).
% 2.73/2.99  thf('63', plain, (((sk_B_1) = (sk_D))),
% 2.73/2.99      inference('clc', [status(thm)], ['61', '62'])).
% 2.73/2.99  thf('64', plain, (((sk_D) != (k1_xboole_0))),
% 2.73/2.99      inference('demod', [status(thm)], ['38', '63'])).
% 2.73/2.99  thf('65', plain, (($false) <= (~ (((sk_A) = (sk_C_1))))),
% 2.73/2.99      inference('simplify_reflect-', [status(thm)], ['37', '64'])).
% 2.73/2.99  thf('66', plain, (((sk_B_1) = (sk_D))),
% 2.73/2.99      inference('clc', [status(thm)], ['61', '62'])).
% 2.73/2.99  thf('67', plain, ((((sk_B_1) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 2.73/2.99      inference('split', [status(esa)], ['34'])).
% 2.73/2.99  thf('68', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 2.73/2.99      inference('sup-', [status(thm)], ['66', '67'])).
% 2.73/2.99  thf('69', plain, ((((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('simplify', [status(thm)], ['68'])).
% 2.73/2.99  thf('70', plain, (~ (((sk_A) = (sk_C_1))) | ~ (((sk_B_1) = (sk_D)))),
% 2.73/2.99      inference('split', [status(esa)], ['34'])).
% 2.73/2.99  thf('71', plain, (~ (((sk_A) = (sk_C_1)))),
% 2.73/2.99      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 2.73/2.99  thf('72', plain, ($false),
% 2.73/2.99      inference('simpl_trail', [status(thm)], ['65', '71'])).
% 2.73/2.99  
% 2.73/2.99  % SZS output end Refutation
% 2.73/2.99  
% 2.73/3.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
