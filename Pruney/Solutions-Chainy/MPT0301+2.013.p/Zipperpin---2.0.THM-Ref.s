%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tv7DdZd5uY

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:01 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 549 expanded)
%              Number of leaves         :   22 ( 166 expanded)
%              Depth                    :   22
%              Number of atoms          : 1083 (4300 expanded)
%              Number of equality atoms :  203 ( 971 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('0',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf(t113_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
      <=> ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_zfmisc_1])).

thf('1',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('4',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,
    ( ( sk_A != o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ( ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B_1 )
     != o_0_0_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != o_0_0_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('12',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,
    ( ( sk_B_1 != o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( sk_B_1 != o_0_0_xboole_0 )
   <= ( sk_B_1 != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( sk_B_1 != o_0_0_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','2'])).

thf('21',plain,
    ( ( sk_A != o_0_0_xboole_0 )
   <= ( sk_A != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('22',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( sk_A != o_0_0_xboole_0 )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = o_0_0_xboole_0 )
    | ( sk_A != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('26',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
    | ( sk_A = o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('33',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
    | ( sk_B_1 != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('37',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
    | ( sk_A != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('38',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('39',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('40',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X34 )
      | ~ ( r2_hidden @ X29 @ X34 )
      | ~ ( r2_hidden @ X30 @ X32 )
      | ( X31
       != ( k4_tarski @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('46',plain,(
    ! [X29: $i,X30: $i,X32: $i,X34: $i] :
      ( ~ ( r2_hidden @ X30 @ X32 )
      | ~ ( r2_hidden @ X29 @ X34 )
      | ( zip_tseitin_0 @ X30 @ X29 @ ( k4_tarski @ X29 @ X30 ) @ X32 @ X34 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X0 ) @ X2 @ ( k4_tarski @ X2 @ ( sk_B @ X0 ) ) @ X0 @ X1 )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ X1 @ X0 )
      | ( X1 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X37 @ X40 )
      | ( X40
       != ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X37 @ ( k2_zfmisc_1 @ X39 @ X38 ) )
      | ~ ( zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ X0 ) @ ( sk_B @ X1 ) ) @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('52',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X46 ) @ X45 )
        = X45 )
      | ~ ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = o_0_0_xboole_0 )
      | ( X0 = o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( k4_tarski @ ( sk_B @ X1 ) @ ( sk_B @ X0 ) ) ) @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( ( k2_xboole_0 @ ( k1_tarski @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ) @ o_0_0_xboole_0 )
        = ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('56',plain,
    ( ( ( ( k2_xboole_0 @ ( k1_tarski @ ( k4_tarski @ ( sk_B @ sk_A ) @ ( sk_B @ sk_B_1 ) ) ) @ o_0_0_xboole_0 )
        = o_0_0_xboole_0 )
      | ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('57',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('58',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('59',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( sk_B_1 = o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['56','59'])).

thf('61',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('62',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,
    ( ( sk_B_1 != o_0_0_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( sk_A = o_0_0_xboole_0 ) )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['60','64'])).

thf('66',plain,
    ( ( sk_A = o_0_0_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('68',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('69',plain,
    ( ( sk_A != o_0_0_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( sk_B_1 != k1_xboole_0 )
      & ( sk_A != k1_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != o_0_0_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','23','35','36','37','71'])).

thf('73',plain,
    ( ( ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B_1 )
     != o_0_0_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['9','72'])).

thf('74',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_B_1 = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('75',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['70'])).

thf('76',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('77',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['7'])).

thf('78',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
       != o_0_0_xboole_0 )
      & ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_B_1 = o_0_0_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('81',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('82',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','23','35','36','37','71','79'])).

thf('83',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ o_0_0_xboole_0 )
     != o_0_0_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( X0 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('86',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X40 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X41 @ X38 @ X39 ) @ ( sk_E_1 @ X41 @ X38 @ X39 ) @ X41 @ X38 @ X39 )
      | ( X40
       != ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,(
    ! [X38: $i,X39: $i,X41: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X41 @ X38 @ X39 ) @ ( sk_E_1 @ X41 @ X38 @ X39 ) @ X41 @ X38 @ X39 )
      | ~ ( r2_hidden @ X41 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ X32 )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X46 ) @ X45 )
        = X45 )
      | ~ ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','95'])).

thf('97',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['1'])).

thf('99',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['74','23','35','36','37','75','79','97','98'])).

thf('100',plain,(
    ( k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B_1 )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['73','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('102',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X29 @ X33 )
      | ~ ( zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X45: $i,X46: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X46 ) @ X45 )
        = X45 )
      | ~ ( r2_hidden @ X46 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = o_0_0_xboole_0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_E_1 @ ( sk_B @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ X1 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ o_0_0_xboole_0 @ X1 )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['100','108'])).

thf('110',plain,(
    $false ),
    inference(simplify,[status(thm)],['109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Tv7DdZd5uY
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:37:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.56  % Solved by: fo/fo7.sh
% 0.38/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.56  % done 241 iterations in 0.103s
% 0.38/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.56  % SZS output start Refutation
% 0.38/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.38/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.56  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.38/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.38/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.56  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.38/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.56  thf(sk_F_1_type, type, sk_F_1: $i > $i > $i > $i).
% 0.38/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.38/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.56  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.38/0.56  thf('0', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf(t113_zfmisc_1, conjecture,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.56    (~( ![A:$i,B:$i]:
% 0.38/0.56        ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.38/0.56          ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.38/0.56    inference('cnf.neg', [status(esa)], [t113_zfmisc_1])).
% 0.38/0.56  thf('1', plain,
% 0.38/0.56      ((((sk_B_1) = (k1_xboole_0))
% 0.38/0.56        | ((sk_A) = (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('2', plain, ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['1'])).
% 0.38/0.56  thf('3', plain,
% 0.38/0.56      ((((sk_A) = (o_0_0_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['0', '2'])).
% 0.38/0.56  thf('4', plain,
% 0.38/0.56      ((((sk_A) != (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('6', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('7', plain,
% 0.38/0.56      ((((sk_A) != (o_0_0_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.38/0.56  thf('8', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('9', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B_1) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))) & 
% 0.38/0.56             (((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['3', '8'])).
% 0.38/0.56  thf('10', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('11', plain,
% 0.38/0.56      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['1'])).
% 0.38/0.56  thf('12', plain,
% 0.38/0.56      ((((sk_B_1) = (o_0_0_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('13', plain,
% 0.38/0.56      ((((sk_B_1) != (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('14', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('16', plain,
% 0.38/0.56      ((((sk_B_1) != (o_0_0_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.38/0.56  thf('17', plain,
% 0.38/0.56      ((((sk_B_1) != (o_0_0_xboole_0))) <= (~ (((sk_B_1) = (o_0_0_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['16'])).
% 0.38/0.56  thf('18', plain,
% 0.38/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((sk_B_1) = (o_0_0_xboole_0))) & (((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['12', '17'])).
% 0.38/0.56  thf('19', plain,
% 0.38/0.56      ((((sk_B_1) = (o_0_0_xboole_0))) | ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.56  thf('20', plain,
% 0.38/0.56      ((((sk_A) = (o_0_0_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['0', '2'])).
% 0.38/0.56  thf('21', plain,
% 0.38/0.56      ((((sk_A) != (o_0_0_xboole_0))) <= (~ (((sk_A) = (o_0_0_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('22', plain,
% 0.38/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((sk_A) = (o_0_0_xboole_0))) & (((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.38/0.56  thf('23', plain,
% 0.38/0.56      ((((sk_A) = (o_0_0_xboole_0))) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.38/0.56  thf('24', plain,
% 0.38/0.56      ((((sk_B_1) = (k1_xboole_0))
% 0.38/0.56        | ((sk_A) = (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('25', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('26', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('27', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('28', plain,
% 0.38/0.56      ((((sk_B_1) = (o_0_0_xboole_0))
% 0.38/0.56        | ((sk_A) = (o_0_0_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 0.38/0.56  thf('29', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['28'])).
% 0.38/0.56  thf('30', plain,
% 0.38/0.56      ((((sk_A) != (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('31', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['30'])).
% 0.38/0.56  thf('32', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('33', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.38/0.56  thf('34', plain,
% 0.38/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.38/0.56             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['29', '33'])).
% 0.38/0.56  thf('35', plain,
% 0.38/0.56      (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))) | 
% 0.38/0.56       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.38/0.56  thf('36', plain,
% 0.38/0.56      (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))) | 
% 0.38/0.56       ~ (((sk_B_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('split', [status(esa)], ['16'])).
% 0.38/0.56  thf('37', plain,
% 0.38/0.56      (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))) | 
% 0.38/0.56       ~ (((sk_A) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('38', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['1'])).
% 0.38/0.56  thf('39', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('40', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf(t7_xboole_0, axiom,
% 0.38/0.56    (![A:$i]:
% 0.38/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.38/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('41', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.38/0.56  thf('42', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('43', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('44', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf(d2_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ?[E:$i,F:$i]:
% 0.38/0.56             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.38/0.56               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.38/0.56  thf(zf_stmt_1, axiom,
% 0.38/0.56    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.56     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.38/0.56       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.38/0.56         ( r2_hidden @ E @ A ) ) ))).
% 0.38/0.56  thf('45', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X34 : $i]:
% 0.38/0.56         ((zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X34)
% 0.38/0.56          | ~ (r2_hidden @ X29 @ X34)
% 0.38/0.56          | ~ (r2_hidden @ X30 @ X32)
% 0.38/0.56          | ((X31) != (k4_tarski @ X29 @ X30)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf('46', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X32 : $i, X34 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X30 @ X32)
% 0.38/0.56          | ~ (r2_hidden @ X29 @ X34)
% 0.38/0.56          | (zip_tseitin_0 @ X30 @ X29 @ (k4_tarski @ X29 @ X30) @ X32 @ X34))),
% 0.38/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.38/0.56  thf('47', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.56         (((X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (zip_tseitin_0 @ (sk_B @ X0) @ X2 @ 
% 0.38/0.56             (k4_tarski @ X2 @ (sk_B @ X0)) @ X0 @ X1)
% 0.38/0.56          | ~ (r2_hidden @ X2 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['44', '46'])).
% 0.38/0.56  thf('48', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (zip_tseitin_0 @ (sk_B @ X1) @ (sk_B @ X0) @ 
% 0.38/0.56             (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ X1 @ X0)
% 0.38/0.56          | ((X1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['43', '47'])).
% 0.38/0.56  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.38/0.56  thf(zf_stmt_3, axiom,
% 0.38/0.56    (![A:$i,B:$i,C:$i]:
% 0.38/0.56     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.38/0.56       ( ![D:$i]:
% 0.38/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.56           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.56  thf('49', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.38/0.56         (~ (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39)
% 0.38/0.56          | (r2_hidden @ X37 @ X40)
% 0.38/0.56          | ((X40) != (k2_zfmisc_1 @ X39 @ X38)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.56  thf('50', plain,
% 0.38/0.56      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.38/0.56         ((r2_hidden @ X37 @ (k2_zfmisc_1 @ X39 @ X38))
% 0.38/0.56          | ~ (zip_tseitin_0 @ X35 @ X36 @ X37 @ X38 @ X39))),
% 0.38/0.56      inference('simplify', [status(thm)], ['49'])).
% 0.38/0.56  thf('51', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X1) = (o_0_0_xboole_0))
% 0.38/0.56          | ((X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (r2_hidden @ (k4_tarski @ (sk_B @ X0) @ (sk_B @ X1)) @ 
% 0.38/0.56             (k2_zfmisc_1 @ X0 @ X1)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['48', '50'])).
% 0.38/0.56  thf(l22_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( r2_hidden @ A @ B ) =>
% 0.38/0.56       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.38/0.56  thf('52', plain,
% 0.38/0.56      (![X45 : $i, X46 : $i]:
% 0.38/0.56         (((k2_xboole_0 @ (k1_tarski @ X46) @ X45) = (X45))
% 0.38/0.56          | ~ (r2_hidden @ X46 @ X45))),
% 0.38/0.56      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.38/0.56  thf('53', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X1) = (o_0_0_xboole_0))
% 0.38/0.56          | ((X0) = (o_0_0_xboole_0))
% 0.38/0.56          | ((k2_xboole_0 @ 
% 0.38/0.56              (k1_tarski @ (k4_tarski @ (sk_B @ X1) @ (sk_B @ X0))) @ 
% 0.38/0.56              (k2_zfmisc_1 @ X1 @ X0)) = (k2_zfmisc_1 @ X1 @ X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.56  thf('54', plain,
% 0.38/0.56      (((((k2_xboole_0 @ 
% 0.38/0.56           (k1_tarski @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1))) @ 
% 0.38/0.56           o_0_0_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.38/0.56         | ((sk_B_1) = (o_0_0_xboole_0))
% 0.38/0.56         | ((sk_A) = (o_0_0_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['40', '53'])).
% 0.38/0.56  thf('55', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf('56', plain,
% 0.38/0.56      (((((k2_xboole_0 @ 
% 0.38/0.56           (k1_tarski @ (k4_tarski @ (sk_B @ sk_A) @ (sk_B @ sk_B_1))) @ 
% 0.38/0.56           o_0_0_xboole_0) = (o_0_0_xboole_0))
% 0.38/0.56         | ((sk_B_1) = (o_0_0_xboole_0))
% 0.38/0.56         | ((sk_A) = (o_0_0_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.38/0.56  thf(t49_zfmisc_1, axiom,
% 0.38/0.56    (![A:$i,B:$i]:
% 0.38/0.56     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.38/0.56  thf('57', plain,
% 0.38/0.56      (![X47 : $i, X48 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k1_tarski @ X47) @ X48) != (k1_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.38/0.56  thf('58', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('59', plain,
% 0.38/0.56      (![X47 : $i, X48 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k1_tarski @ X47) @ X48) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.38/0.56  thf('60', plain,
% 0.38/0.56      (((((sk_B_1) = (o_0_0_xboole_0)) | ((sk_A) = (o_0_0_xboole_0))))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify_reflect-', [status(thm)], ['56', '59'])).
% 0.38/0.56  thf('61', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('62', plain,
% 0.38/0.56      ((((sk_B_1) != (k1_xboole_0))
% 0.38/0.56        | ((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.56  thf('63', plain,
% 0.38/0.56      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['62'])).
% 0.38/0.56  thf('64', plain,
% 0.38/0.56      ((((sk_B_1) != (o_0_0_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['61', '63'])).
% 0.38/0.56  thf('65', plain,
% 0.38/0.56      (((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | ((sk_A) = (o_0_0_xboole_0))))
% 0.38/0.56         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.38/0.56             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['60', '64'])).
% 0.38/0.56  thf('66', plain,
% 0.38/0.56      ((((sk_A) = (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.38/0.56             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('simplify', [status(thm)], ['65'])).
% 0.38/0.56  thf('67', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.38/0.56  thf('68', plain,
% 0.38/0.56      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['30'])).
% 0.38/0.56  thf('69', plain,
% 0.38/0.56      ((((sk_A) != (o_0_0_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.38/0.56  thf('70', plain,
% 0.38/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((sk_B_1) = (k1_xboole_0))) & 
% 0.38/0.56             ~ (((sk_A) = (k1_xboole_0))) & 
% 0.38/0.56             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['66', '69'])).
% 0.38/0.56  thf('71', plain,
% 0.38/0.56      ((((sk_A) = (k1_xboole_0))) | 
% 0.38/0.56       ~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.38/0.56       (((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.56  thf('72', plain, (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)],
% 0.38/0.56                ['19', '23', '35', '36', '37', '71'])).
% 0.38/0.56  thf('73', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B_1) != (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((sk_A) = (k1_xboole_0))))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['9', '72'])).
% 0.38/0.56  thf('74', plain,
% 0.38/0.56      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_B_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.38/0.56  thf('75', plain,
% 0.38/0.56      (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.38/0.56       (((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['70'])).
% 0.38/0.56  thf('76', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['38', '39'])).
% 0.38/0.56  thf('77', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))))),
% 0.38/0.56      inference('split', [status(esa)], ['7'])).
% 0.38/0.56  thf('78', plain,
% 0.38/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0))) & 
% 0.38/0.56             (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.38/0.56  thf('79', plain,
% 0.38/0.56      (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.38/0.56       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['78'])).
% 0.38/0.56  thf('80', plain,
% 0.38/0.56      ((((sk_B_1) = (o_0_0_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup+', [status(thm)], ['10', '11'])).
% 0.38/0.56  thf('81', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0)))
% 0.38/0.56         <= (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.38/0.56  thf('82', plain, (~ (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)],
% 0.38/0.56                ['19', '23', '35', '36', '37', '71', '79'])).
% 0.38/0.56  thf('83', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['81', '82'])).
% 0.38/0.56  thf('84', plain,
% 0.38/0.56      ((((k2_zfmisc_1 @ sk_A @ o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('sup-', [status(thm)], ['80', '83'])).
% 0.38/0.56  thf('85', plain,
% 0.38/0.56      (![X0 : $i]: (((X0) = (o_0_0_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.38/0.56      inference('demod', [status(thm)], ['41', '42'])).
% 0.38/0.56  thf('86', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.38/0.56         (~ (r2_hidden @ X41 @ X40)
% 0.38/0.56          | (zip_tseitin_0 @ (sk_F_1 @ X41 @ X38 @ X39) @ 
% 0.38/0.56             (sk_E_1 @ X41 @ X38 @ X39) @ X41 @ X38 @ X39)
% 0.38/0.56          | ((X40) != (k2_zfmisc_1 @ X39 @ X38)))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.56  thf('87', plain,
% 0.38/0.56      (![X38 : $i, X39 : $i, X41 : $i]:
% 0.38/0.56         ((zip_tseitin_0 @ (sk_F_1 @ X41 @ X38 @ X39) @ 
% 0.38/0.56           (sk_E_1 @ X41 @ X38 @ X39) @ X41 @ X38 @ X39)
% 0.38/0.56          | ~ (r2_hidden @ X41 @ (k2_zfmisc_1 @ X39 @ X38)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['86'])).
% 0.38/0.56  thf('88', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (zip_tseitin_0 @ 
% 0.38/0.56             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.38/0.56             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.38/0.56             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['85', '87'])).
% 0.38/0.56  thf('89', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.56         ((r2_hidden @ X30 @ X32)
% 0.38/0.56          | ~ (zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf('90', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X0 @ X1) = (o_0_0_xboole_0))
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['88', '89'])).
% 0.38/0.56  thf('91', plain,
% 0.38/0.56      (![X45 : $i, X46 : $i]:
% 0.38/0.56         (((k2_xboole_0 @ (k1_tarski @ X46) @ X45) = (X45))
% 0.38/0.56          | ~ (r2_hidden @ X46 @ X45))),
% 0.38/0.56      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.38/0.56  thf('92', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.38/0.56          | ((k2_xboole_0 @ 
% 0.38/0.56              (k1_tarski @ 
% 0.38/0.56               (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1)) @ 
% 0.38/0.56              X0) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['90', '91'])).
% 0.38/0.56  thf('93', plain,
% 0.38/0.56      (![X47 : $i, X48 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k1_tarski @ X47) @ X48) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.38/0.56  thf('94', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) != (o_0_0_xboole_0))
% 0.38/0.56          | ((k2_zfmisc_1 @ X1 @ X0) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['92', '93'])).
% 0.38/0.56  thf('95', plain,
% 0.38/0.56      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['94'])).
% 0.38/0.56  thf('96', plain,
% 0.38/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.38/0.56         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.38/0.56      inference('demod', [status(thm)], ['84', '95'])).
% 0.38/0.56  thf('97', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('simplify', [status(thm)], ['96'])).
% 0.38/0.56  thf('98', plain,
% 0.38/0.56      ((((sk_A) = (k1_xboole_0))) | (((sk_B_1) = (k1_xboole_0))) | 
% 0.38/0.56       (((k2_zfmisc_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.38/0.56      inference('split', [status(esa)], ['1'])).
% 0.38/0.56  thf('99', plain, ((((sk_A) = (k1_xboole_0)))),
% 0.38/0.56      inference('sat_resolution*', [status(thm)],
% 0.38/0.56                ['74', '23', '35', '36', '37', '75', '79', '97', '98'])).
% 0.38/0.56  thf('100', plain,
% 0.38/0.56      (((k2_zfmisc_1 @ o_0_0_xboole_0 @ sk_B_1) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('simpl_trail', [status(thm)], ['73', '99'])).
% 0.38/0.56  thf('101', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.38/0.56          | (zip_tseitin_0 @ 
% 0.38/0.56             (sk_F_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.38/0.56             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1) @ 
% 0.38/0.56             (sk_B @ (k2_zfmisc_1 @ X1 @ X0)) @ X0 @ X1))),
% 0.38/0.56      inference('sup-', [status(thm)], ['85', '87'])).
% 0.38/0.56  thf('102', plain,
% 0.38/0.56      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.56         ((r2_hidden @ X29 @ X33)
% 0.38/0.56          | ~ (zip_tseitin_0 @ X30 @ X29 @ X31 @ X32 @ X33))),
% 0.38/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.56  thf('103', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X0 @ X1) = (o_0_0_xboole_0))
% 0.38/0.56          | (r2_hidden @ 
% 0.38/0.56             (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0) @ X0))),
% 0.38/0.56      inference('sup-', [status(thm)], ['101', '102'])).
% 0.38/0.56  thf('104', plain,
% 0.38/0.56      (![X45 : $i, X46 : $i]:
% 0.38/0.56         (((k2_xboole_0 @ (k1_tarski @ X46) @ X45) = (X45))
% 0.38/0.56          | ~ (r2_hidden @ X46 @ X45))),
% 0.38/0.56      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.38/0.56  thf('105', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((k2_zfmisc_1 @ X0 @ X1) = (o_0_0_xboole_0))
% 0.38/0.56          | ((k2_xboole_0 @ 
% 0.38/0.56              (k1_tarski @ 
% 0.38/0.56               (sk_E_1 @ (sk_B @ (k2_zfmisc_1 @ X0 @ X1)) @ X1 @ X0)) @ 
% 0.38/0.56              X0) = (X0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['103', '104'])).
% 0.38/0.56  thf('106', plain,
% 0.38/0.56      (![X47 : $i, X48 : $i]:
% 0.38/0.56         ((k2_xboole_0 @ (k1_tarski @ X47) @ X48) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['57', '58'])).
% 0.38/0.56  thf('107', plain,
% 0.38/0.56      (![X0 : $i, X1 : $i]:
% 0.38/0.56         (((X0) != (o_0_0_xboole_0))
% 0.38/0.56          | ((k2_zfmisc_1 @ X0 @ X1) = (o_0_0_xboole_0)))),
% 0.38/0.56      inference('sup-', [status(thm)], ['105', '106'])).
% 0.38/0.56  thf('108', plain,
% 0.38/0.56      (![X1 : $i]: ((k2_zfmisc_1 @ o_0_0_xboole_0 @ X1) = (o_0_0_xboole_0))),
% 0.38/0.56      inference('simplify', [status(thm)], ['107'])).
% 0.38/0.56  thf('109', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.38/0.56      inference('demod', [status(thm)], ['100', '108'])).
% 0.38/0.56  thf('110', plain, ($false), inference('simplify', [status(thm)], ['109'])).
% 0.38/0.56  
% 0.38/0.56  % SZS output end Refutation
% 0.38/0.56  
% 0.38/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
