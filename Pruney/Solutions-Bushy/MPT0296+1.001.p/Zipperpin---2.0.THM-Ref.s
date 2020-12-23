%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0296+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9x7UZPIcqN

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:51:40 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 327 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   17
%              Number of atoms          :  705 (4019 expanded)
%              Number of equality atoms :   47 ( 244 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t104_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ~ ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) )
        & ! [F: $i,G: $i] :
            ~ ( ( A
                = ( k4_tarski @ F @ G ) )
              & ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) )
              & ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ~ ( ( r2_hidden @ A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ B @ C ) @ ( k2_zfmisc_1 @ D @ E ) ) )
          & ! [F: $i,G: $i] :
              ~ ( ( A
                  = ( k4_tarski @ F @ G ) )
                & ( r2_hidden @ F @ ( k3_xboole_0 @ B @ D ) )
                & ( r2_hidden @ G @ ( k3_xboole_0 @ C @ E ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t104_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ X20 @ X17 )
      | ( X19
       != ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('2',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ X20 @ X17 )
      | ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','2'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ( X11
       != ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['3','5'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('11',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r2_hidden @ X20 @ X18 )
      | ( X19
       != ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_D_2 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X9: $i,X10: $i,X12: $i] :
      ( ( zip_tseitin_0 @ ( sk_F_1 @ X12 @ X9 @ X10 ) @ ( sk_E_1 @ X12 @ X9 @ X10 ) @ X12 @ X9 @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k2_zfmisc_1 @ X10 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_A @ sk_E_2 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X2
        = ( k4_tarski @ X0 @ X1 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X23 = X22 )
      | ( ( k4_tarski @ X23 @ X25 )
       != ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('22',plain,(
    ! [X23: $i,X25: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X23 @ X25 ) )
      = X23 ) ),
    inference(inj_rec,[status(thm)],['21'])).

thf('23',plain,
    ( ( '#_fresh_sk1' @ sk_A )
    = ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( sk_A
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','23'])).

thf('25',plain,
    ( sk_A
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A ) @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','23'])).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_tarski @ X23 @ X25 )
       != ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('27',plain,(
    ! [X23: $i,X25: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X23 @ X25 ) )
      = X25 ) ),
    inference(inj_rec,[status(thm)],['26'])).

thf('28',plain,
    ( ( '#_fresh_sk2' @ sk_A )
    = ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,
    ( sk_A
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A ) @ ( '#_fresh_sk2' @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','28'])).

thf('30',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X25 = X24 )
      | ( ( k4_tarski @ X23 @ X25 )
       != ( k4_tarski @ X22 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_tarski @ X1 @ X0 )
       != sk_A )
      | ( X0
        = ( '#_fresh_sk2' @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A != sk_A )
    | ( ( sk_F_1 @ sk_A @ sk_C @ sk_B )
      = ( '#_fresh_sk2' @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','31'])).

thf('33',plain,
    ( ( sk_F_1 @ sk_A @ sk_C @ sk_B )
    = ( '#_fresh_sk2' @ sk_A ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r2_hidden @ ( '#_fresh_sk2' @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['8','33'])).

thf('35',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_A @ sk_E_2 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X1 @ X3 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    r2_hidden @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_E_2 ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( '#_fresh_sk2' @ sk_A )
    = ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('39',plain,(
    r2_hidden @ ( '#_fresh_sk2' @ sk_A ) @ sk_E_2 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ( r2_hidden @ X16 @ X19 )
      | ( X19
       != ( k3_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( '#_fresh_sk2' @ sk_A ) @ X0 )
      | ( r2_hidden @ ( '#_fresh_sk2' @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    r2_hidden @ ( '#_fresh_sk2' @ sk_A ) @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_A @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['3','5'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('46',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_1 @ sk_A @ sk_C @ sk_B ) @ ( sk_F_1 @ sk_A @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('48',plain,(
    ! [X23: $i,X25: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X23 @ X25 ) )
      = X23 ) ),
    inference(inj_rec,[status(thm)],['21'])).

thf('49',plain,
    ( ( '#_fresh_sk1' @ sk_A )
    = ( sk_E_1 @ sk_A @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( '#_fresh_sk1' @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    zip_tseitin_0 @ ( sk_F_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_A @ sk_E_2 @ sk_D_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X0 @ X4 )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X2 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('53',plain,(
    r2_hidden @ ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) @ sk_D_2 ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( '#_fresh_sk1' @ sk_A )
    = ( sk_E_1 @ sk_A @ sk_E_2 @ sk_D_2 ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('55',plain,(
    r2_hidden @ ( '#_fresh_sk1' @ sk_A ) @ sk_D_2 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k3_xboole_0 @ X17 @ X18 ) )
      | ~ ( r2_hidden @ X16 @ X18 )
      | ~ ( r2_hidden @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( '#_fresh_sk1' @ sk_A ) @ X0 )
      | ( r2_hidden @ ( '#_fresh_sk1' @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ ( '#_fresh_sk1' @ sk_A ) @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k3_xboole_0 @ sk_B @ sk_D_2 ) )
      | ~ ( r2_hidden @ X27 @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) )
      | ( sk_A
       != ( k4_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( '#_fresh_sk1' @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_C @ sk_E_2 ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    sk_A
 != ( k4_tarski @ ( '#_fresh_sk1' @ sk_A ) @ ( '#_fresh_sk2' @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','60'])).

thf('62',plain,
    ( sk_A
    = ( k4_tarski @ ( '#_fresh_sk1' @ sk_A ) @ ( '#_fresh_sk2' @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','28'])).

thf('63',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).


%------------------------------------------------------------------------------
