%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XcP1cZSUkv

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:38 EST 2020

% Result     : Theorem 0.85s
% Output     : Refutation 0.85s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 212 expanded)
%              Number of leaves         :   16 (  69 expanded)
%              Depth                    :   19
%              Number of atoms          :  684 (2173 expanded)
%              Number of equality atoms :   65 ( 279 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X12 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
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
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( sk_D = k1_xboole_0 )
      | ( r1_tarski @ sk_C_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,
    ( ( r1_tarski @ sk_C_1 @ sk_A )
    | ( sk_D = k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( r1_tarski @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,
    ( ( sk_D = k1_xboole_0 )
    | ~ ( r1_tarski @ sk_A @ sk_C_1 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_B @ X2 ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,
    ( ( r1_tarski @ sk_A @ sk_C_1 )
    | ( r1_tarski @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_A @ sk_C_1 ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference(demod,[status(thm)],['13','23'])).

thf('25',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_A != sk_C_1 )
   <= ( sk_A != sk_C_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['31','32','33'])).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('36',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X12 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,
    ( ( r1_tarski @ sk_D @ sk_B_1 )
    | ( r1_tarski @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ sk_D @ sk_B_1 ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ sk_D )
    | ( sk_B_1 = sk_D ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
    = ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_C @ X1 @ X0 ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_C @ X2 @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_C @ X0 @ sk_B_1 ) ) @ ( k2_zfmisc_1 @ sk_C_1 @ sk_D ) )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( k2_zfmisc_1 @ X9 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_1 ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,
    ( ( r1_tarski @ sk_B_1 @ sk_D )
    | ( r1_tarski @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    r1_tarski @ sk_B_1 @ sk_D ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_B_1 = sk_D ),
    inference(demod,[status(thm)],['49','61'])).

thf('63',plain,
    ( ( sk_B_1 != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('64',plain,
    ( ( sk_D != sk_D )
   <= ( sk_B_1 != sk_D ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    sk_B_1 = sk_D ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( sk_A != sk_C_1 )
    | ( sk_B_1 != sk_D ) ),
    inference(split,[status(esa)],['25'])).

thf('67',plain,(
    sk_A != sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A != sk_C_1 ),
    inference(simpl_trail,[status(thm)],['26','67'])).

thf('69',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','68'])).

thf('70',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    sk_B_1 = sk_D ),
    inference(demod,[status(thm)],['49','61'])).

thf('73',plain,(
    sk_D != k1_xboole_0 ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XcP1cZSUkv
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:03:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.85/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.85/1.03  % Solved by: fo/fo7.sh
% 0.85/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.85/1.03  % done 456 iterations in 0.594s
% 0.85/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.85/1.03  % SZS output start Refutation
% 0.85/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.85/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.85/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.85/1.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.85/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.85/1.03  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.85/1.03  thf(sk_D_type, type, sk_D: $i).
% 0.85/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.85/1.03  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.85/1.03  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.85/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.85/1.03  thf(d3_tarski, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( r1_tarski @ A @ B ) <=>
% 0.85/1.03       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.85/1.03  thf('0', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf(t7_xboole_0, axiom,
% 0.85/1.03    (![A:$i]:
% 0.85/1.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.85/1.03          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.85/1.03  thf('1', plain,
% 0.85/1.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.85/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.85/1.03  thf(l54_zfmisc_1, axiom,
% 0.85/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.85/1.03       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.85/1.03  thf('2', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X12))
% 0.85/1.03          | ~ (r2_hidden @ X10 @ X12)
% 0.85/1.03          | ~ (r2_hidden @ X8 @ X9))),
% 0.85/1.03      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.03  thf('3', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((X0) = (k1_xboole_0))
% 0.85/1.03          | ~ (r2_hidden @ X2 @ X1)
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.85/1.03  thf('4', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ((r1_tarski @ X0 @ X1)
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X0 @ X2))
% 0.85/1.03          | ((X2) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['0', '3'])).
% 0.85/1.03  thf(t134_zfmisc_1, conjecture,
% 0.85/1.03    (![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.85/1.03       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.03         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.85/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.85/1.03    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.85/1.03        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.85/1.03          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.85/1.03            ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) )),
% 0.85/1.03    inference('cnf.neg', [status(esa)], [t134_zfmisc_1])).
% 0.85/1.03  thf('5', plain,
% 0.85/1.03      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('6', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.03         ((r2_hidden @ X8 @ X9)
% 0.85/1.03          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.03  thf('7', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.03          | (r2_hidden @ X1 @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['5', '6'])).
% 0.85/1.03  thf('8', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         (((sk_D) = (k1_xboole_0))
% 0.85/1.03          | (r1_tarski @ sk_C_1 @ X0)
% 0.85/1.03          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['4', '7'])).
% 0.85/1.03  thf('9', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('10', plain,
% 0.85/1.03      (((r1_tarski @ sk_C_1 @ sk_A)
% 0.85/1.03        | ((sk_D) = (k1_xboole_0))
% 0.85/1.03        | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.85/1.03      inference('sup-', [status(thm)], ['8', '9'])).
% 0.85/1.03  thf('11', plain, ((((sk_D) = (k1_xboole_0)) | (r1_tarski @ sk_C_1 @ sk_A))),
% 0.85/1.03      inference('simplify', [status(thm)], ['10'])).
% 0.85/1.03  thf(d10_xboole_0, axiom,
% 0.85/1.03    (![A:$i,B:$i]:
% 0.85/1.03     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.85/1.03  thf('12', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('13', plain,
% 0.85/1.03      ((((sk_D) = (k1_xboole_0))
% 0.85/1.03        | ~ (r1_tarski @ sk_A @ sk_C_1)
% 0.85/1.03        | ((sk_A) = (sk_C_1)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['11', '12'])).
% 0.85/1.03  thf('14', plain,
% 0.85/1.03      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('15', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         ((r1_tarski @ X0 @ X1)
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_B @ X2)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X0 @ X2))
% 0.85/1.03          | ((X2) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['0', '3'])).
% 0.85/1.03  thf('16', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.85/1.03           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.03          | ((sk_B_1) = (k1_xboole_0))
% 0.85/1.03          | (r1_tarski @ sk_A @ X0))),
% 0.85/1.03      inference('sup+', [status(thm)], ['14', '15'])).
% 0.85/1.03  thf('17', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('18', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ (sk_C @ X0 @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.85/1.03           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.03          | (r1_tarski @ sk_A @ X0))),
% 0.85/1.03      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.85/1.03  thf('19', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.03         ((r2_hidden @ X8 @ X9)
% 0.85/1.03          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.03  thf('20', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_C_1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['18', '19'])).
% 0.85/1.03  thf('21', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('22', plain,
% 0.85/1.03      (((r1_tarski @ sk_A @ sk_C_1) | (r1_tarski @ sk_A @ sk_C_1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['20', '21'])).
% 0.85/1.03  thf('23', plain, ((r1_tarski @ sk_A @ sk_C_1)),
% 0.85/1.03      inference('simplify', [status(thm)], ['22'])).
% 0.85/1.03  thf('24', plain, ((((sk_D) = (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 0.85/1.03      inference('demod', [status(thm)], ['13', '23'])).
% 0.85/1.03  thf('25', plain, ((((sk_A) != (sk_C_1)) | ((sk_B_1) != (sk_D)))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('26', plain, ((((sk_A) != (sk_C_1))) <= (~ (((sk_A) = (sk_C_1))))),
% 0.85/1.03      inference('split', [status(esa)], ['25'])).
% 0.85/1.03  thf('27', plain,
% 0.85/1.03      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('28', plain,
% 0.85/1.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.85/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.85/1.03  thf('29', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((X0) = (k1_xboole_0))
% 0.85/1.03          | ~ (r2_hidden @ X2 @ X1)
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ X2 @ (sk_B @ X0)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X1 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.85/1.03  thf('30', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (((X0) = (k1_xboole_0))
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X0 @ X1))
% 0.85/1.03          | ((X1) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['28', '29'])).
% 0.85/1.03  thf('31', plain,
% 0.85/1.03      (((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.85/1.03         (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.03        | ((sk_B_1) = (k1_xboole_0))
% 0.85/1.03        | ((sk_A) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['27', '30'])).
% 0.85/1.03  thf('32', plain, (((sk_A) != (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('34', plain,
% 0.85/1.03      ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1)) @ 
% 0.85/1.03        (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.85/1.03      inference('simplify_reflect-', [status(thm)], ['31', '32', '33'])).
% 0.85/1.03  thf('35', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.03         ((r2_hidden @ X8 @ X9)
% 0.85/1.03          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.03  thf('36', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_C_1)),
% 0.85/1.03      inference('sup-', [status(thm)], ['34', '35'])).
% 0.85/1.03  thf('37', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('38', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X12))
% 0.85/1.03          | ~ (r2_hidden @ X10 @ X12)
% 0.85/1.03          | ~ (r2_hidden @ X8 @ X9))),
% 0.85/1.03      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.03  thf('39', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X0 @ X1)
% 0.85/1.03          | ~ (r2_hidden @ X3 @ X2)
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.85/1.03  thf('40', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X1 @ X0)) @ 
% 0.85/1.03           (k2_zfmisc_1 @ sk_C_1 @ X0))
% 0.85/1.03          | (r1_tarski @ X0 @ X1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['36', '39'])).
% 0.85/1.03  thf('41', plain,
% 0.85/1.03      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('42', plain,
% 0.85/1.03      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.03         ((r2_hidden @ X10 @ X11)
% 0.85/1.03          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.85/1.03      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.03  thf('43', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i]:
% 0.85/1.03         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.03          | (r2_hidden @ X0 @ sk_B_1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['41', '42'])).
% 0.85/1.03  thf('44', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r1_tarski @ sk_D @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_D) @ sk_B_1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['40', '43'])).
% 0.85/1.03  thf('45', plain,
% 0.85/1.03      (![X1 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.03      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.03  thf('46', plain,
% 0.85/1.03      (((r1_tarski @ sk_D @ sk_B_1) | (r1_tarski @ sk_D @ sk_B_1))),
% 0.85/1.03      inference('sup-', [status(thm)], ['44', '45'])).
% 0.85/1.03  thf('47', plain, ((r1_tarski @ sk_D @ sk_B_1)),
% 0.85/1.03      inference('simplify', [status(thm)], ['46'])).
% 0.85/1.03  thf('48', plain,
% 0.85/1.03      (![X5 : $i, X7 : $i]:
% 0.85/1.03         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.85/1.03      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.85/1.03  thf('49', plain, ((~ (r1_tarski @ sk_B_1 @ sk_D) | ((sk_B_1) = (sk_D)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.85/1.03  thf('50', plain,
% 0.85/1.03      (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k2_zfmisc_1 @ sk_C_1 @ sk_D))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('51', plain,
% 0.85/1.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.85/1.03      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.85/1.03  thf('52', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.85/1.03         ((r1_tarski @ X0 @ X1)
% 0.85/1.03          | ~ (r2_hidden @ X3 @ X2)
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ X3 @ (sk_C @ X1 @ X0)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.85/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.85/1.03  thf('53', plain,
% 0.85/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.85/1.03         (((X0) = (k1_xboole_0))
% 0.85/1.03          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_C @ X2 @ X1)) @ 
% 0.85/1.03             (k2_zfmisc_1 @ X0 @ X1))
% 0.85/1.03          | (r1_tarski @ X1 @ X2))),
% 0.85/1.03      inference('sup-', [status(thm)], ['51', '52'])).
% 0.85/1.03  thf('54', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.85/1.03           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.03          | (r1_tarski @ sk_B_1 @ X0)
% 0.85/1.03          | ((sk_A) = (k1_xboole_0)))),
% 0.85/1.03      inference('sup+', [status(thm)], ['50', '53'])).
% 0.85/1.03  thf('55', plain, (((sk_A) != (k1_xboole_0))),
% 0.85/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.03  thf('56', plain,
% 0.85/1.03      (![X0 : $i]:
% 0.85/1.03         ((r2_hidden @ (k4_tarski @ (sk_B @ sk_A) @ (sk_C @ X0 @ sk_B_1)) @ 
% 0.85/1.04           (k2_zfmisc_1 @ sk_C_1 @ sk_D))
% 0.85/1.04          | (r1_tarski @ sk_B_1 @ X0))),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.85/1.04  thf('57', plain,
% 0.85/1.04      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.85/1.04         ((r2_hidden @ X10 @ X11)
% 0.85/1.04          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (k2_zfmisc_1 @ X9 @ X11)))),
% 0.85/1.04      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.85/1.04  thf('58', plain,
% 0.85/1.04      (![X0 : $i]:
% 0.85/1.04         ((r1_tarski @ sk_B_1 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_1) @ sk_D))),
% 0.85/1.04      inference('sup-', [status(thm)], ['56', '57'])).
% 0.85/1.04  thf('59', plain,
% 0.85/1.04      (![X1 : $i, X3 : $i]:
% 0.85/1.04         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.85/1.04      inference('cnf', [status(esa)], [d3_tarski])).
% 0.85/1.04  thf('60', plain,
% 0.85/1.04      (((r1_tarski @ sk_B_1 @ sk_D) | (r1_tarski @ sk_B_1 @ sk_D))),
% 0.85/1.04      inference('sup-', [status(thm)], ['58', '59'])).
% 0.85/1.04  thf('61', plain, ((r1_tarski @ sk_B_1 @ sk_D)),
% 0.85/1.04      inference('simplify', [status(thm)], ['60'])).
% 0.85/1.04  thf('62', plain, (((sk_B_1) = (sk_D))),
% 0.85/1.04      inference('demod', [status(thm)], ['49', '61'])).
% 0.85/1.04  thf('63', plain, ((((sk_B_1) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.85/1.04      inference('split', [status(esa)], ['25'])).
% 0.85/1.04  thf('64', plain, ((((sk_D) != (sk_D))) <= (~ (((sk_B_1) = (sk_D))))),
% 0.85/1.04      inference('sup-', [status(thm)], ['62', '63'])).
% 0.85/1.04  thf('65', plain, ((((sk_B_1) = (sk_D)))),
% 0.85/1.04      inference('simplify', [status(thm)], ['64'])).
% 0.85/1.04  thf('66', plain, (~ (((sk_A) = (sk_C_1))) | ~ (((sk_B_1) = (sk_D)))),
% 0.85/1.04      inference('split', [status(esa)], ['25'])).
% 0.85/1.04  thf('67', plain, (~ (((sk_A) = (sk_C_1)))),
% 0.85/1.04      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.85/1.04  thf('68', plain, (((sk_A) != (sk_C_1))),
% 0.85/1.04      inference('simpl_trail', [status(thm)], ['26', '67'])).
% 0.85/1.04  thf('69', plain, ((((sk_C_1) != (sk_C_1)) | ((sk_D) = (k1_xboole_0)))),
% 0.85/1.04      inference('sup-', [status(thm)], ['24', '68'])).
% 0.85/1.04  thf('70', plain, (((sk_D) = (k1_xboole_0))),
% 0.85/1.04      inference('simplify', [status(thm)], ['69'])).
% 0.85/1.04  thf('71', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.85/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.85/1.04  thf('72', plain, (((sk_B_1) = (sk_D))),
% 0.85/1.04      inference('demod', [status(thm)], ['49', '61'])).
% 0.85/1.04  thf('73', plain, (((sk_D) != (k1_xboole_0))),
% 0.85/1.04      inference('demod', [status(thm)], ['71', '72'])).
% 0.85/1.04  thf('74', plain, ($false),
% 0.85/1.04      inference('simplify_reflect-', [status(thm)], ['70', '73'])).
% 0.85/1.04  
% 0.85/1.04  % SZS output end Refutation
% 0.85/1.04  
% 0.85/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
