%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PF8jvnYnU9

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:47 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 239 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  734 (2342 expanded)
%              Number of equality atoms :   66 ( 238 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t20_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
      <=> ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t20_zfmisc_1])).

thf('9',plain,
    ( ( sk_A = sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_A != sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('20',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('21',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = sk_B )
   <= ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('24',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
      = ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X9: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ( ( k4_xboole_0 @ X9 @ X11 )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('26',plain,
    ( ( ( ( k1_tarski @ sk_B )
       != ( k1_tarski @ sk_B ) )
      | ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('35',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ~ ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('36',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_B @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
        = ( k1_tarski @ sk_A ) )
      & ( sk_A = sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A != sk_B ) ),
    inference('sup-',[status(thm)],['19','36'])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_B ) ),
    inference(split,[status(esa)],['9'])).

thf('39',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','37','38'])).

thf('40',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['16','39'])).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( r1_tarski @ X25 @ X23 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('42',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_A != sk_B )
   <= ( sk_A != sk_B ) ),
    inference(split,[status(esa)],['17'])).

thf('47',plain,(
    sk_A != sk_B ),
    inference('sat_resolution*',[status(thm)],['18','37'])).

thf('48',plain,(
    sk_A != sk_B ),
    inference(simpl_trail,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('61',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['18','37','38'])).

thf('62',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','56'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('67',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    r2_hidden @ sk_A @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('72',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['49','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PF8jvnYnU9
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:37:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.34/0.52  % Solved by: fo/fo7.sh
% 0.34/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.52  % done 102 iterations in 0.055s
% 0.34/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.34/0.52  % SZS output start Refutation
% 0.34/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.34/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.34/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.34/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.34/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.52  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.34/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.34/0.52  thf(d10_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.34/0.52  thf('0', plain,
% 0.34/0.52      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('1', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.34/0.52      inference('simplify', [status(thm)], ['0'])).
% 0.34/0.52  thf(d1_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.34/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.34/0.52  thf('2', plain,
% 0.34/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.34/0.52         (~ (r1_tarski @ X22 @ X23)
% 0.34/0.52          | (r2_hidden @ X22 @ X24)
% 0.34/0.52          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.34/0.52  thf('3', plain,
% 0.34/0.52      (![X22 : $i, X23 : $i]:
% 0.34/0.52         ((r2_hidden @ X22 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X22 @ X23))),
% 0.34/0.52      inference('simplify', [status(thm)], ['2'])).
% 0.34/0.52  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.34/0.52  thf(l27_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.34/0.52  thf('5', plain,
% 0.34/0.52      (![X29 : $i, X30 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.34/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.34/0.52  thf('6', plain,
% 0.34/0.52      (![X29 : $i, X30 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.34/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.34/0.52  thf(t83_xboole_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.34/0.52  thf('7', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.52  thf('8', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ X1 @ X0)
% 0.34/0.52          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['6', '7'])).
% 0.34/0.52  thf(t20_zfmisc_1, conjecture,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.34/0.52         ( k1_tarski @ A ) ) <=>
% 0.34/0.52       ( ( A ) != ( B ) ) ))).
% 0.34/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.52    (~( ![A:$i,B:$i]:
% 0.34/0.52        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.34/0.52            ( k1_tarski @ A ) ) <=>
% 0.34/0.52          ( ( A ) != ( B ) ) ) )),
% 0.34/0.52    inference('cnf.neg', [status(esa)], [t20_zfmisc_1])).
% 0.34/0.52  thf('9', plain,
% 0.34/0.52      ((((sk_A) = (sk_B))
% 0.34/0.52        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52            != (k1_tarski @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('10', plain,
% 0.34/0.52      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          != (k1_tarski @ sk_A)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('11', plain,
% 0.34/0.52      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.34/0.52         | (r2_hidden @ sk_A @ (k1_tarski @ sk_B))))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['8', '10'])).
% 0.34/0.52  thf('12', plain,
% 0.34/0.52      (((r2_hidden @ sk_A @ (k1_tarski @ sk_B)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.34/0.52  thf(t3_xboole_0, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.34/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.34/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.34/0.52  thf('13', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('14', plain,
% 0.34/0.52      ((![X0 : $i]:
% 0.34/0.52          (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.34/0.52           | ~ (r2_hidden @ sk_A @ X0)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.34/0.52  thf('15', plain,
% 0.34/0.52      ((![X0 : $i]: ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['5', '14'])).
% 0.34/0.52  thf('16', plain,
% 0.34/0.52      (((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['4', '15'])).
% 0.34/0.52  thf('17', plain,
% 0.34/0.52      ((((sk_A) != (sk_B))
% 0.34/0.52        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52            = (k1_tarski @ sk_A)))),
% 0.34/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.52  thf('18', plain,
% 0.34/0.52      (~ (((sk_A) = (sk_B))) | 
% 0.34/0.52       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A)))),
% 0.34/0.52      inference('split', [status(esa)], ['17'])).
% 0.34/0.52  thf('19', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.34/0.52  thf('20', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('21', plain,
% 0.34/0.52      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A)))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('split', [status(esa)], ['17'])).
% 0.34/0.52  thf('22', plain,
% 0.34/0.52      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A)))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))) & 
% 0.34/0.52             (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('sup+', [status(thm)], ['20', '21'])).
% 0.34/0.52  thf('23', plain, ((((sk_A) = (sk_B))) <= ((((sk_A) = (sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('24', plain,
% 0.34/0.52      ((((k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_B)))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))) & 
% 0.34/0.52             (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('demod', [status(thm)], ['22', '23'])).
% 0.34/0.52  thf('25', plain,
% 0.34/0.52      (![X9 : $i, X11 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X9 @ X11) | ((k4_xboole_0 @ X9 @ X11) != (X9)))),
% 0.34/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.52  thf('26', plain,
% 0.34/0.52      (((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.34/0.52         | (r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))) & 
% 0.34/0.52             (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.34/0.52  thf('27', plain,
% 0.34/0.52      (((r1_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))) & 
% 0.34/0.52             (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.34/0.52  thf('28', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('29', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('30', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('31', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.34/0.52          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.34/0.52  thf('32', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.34/0.52          | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['28', '31'])).
% 0.34/0.52  thf('33', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('simplify', [status(thm)], ['32'])).
% 0.34/0.52  thf('34', plain,
% 0.34/0.52      ((![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))) & 
% 0.34/0.52             (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['27', '33'])).
% 0.34/0.52  thf(l24_zfmisc_1, axiom,
% 0.34/0.52    (![A:$i,B:$i]:
% 0.34/0.52     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.34/0.52  thf('35', plain,
% 0.34/0.52      (![X27 : $i, X28 : $i]:
% 0.34/0.52         (~ (r1_xboole_0 @ (k1_tarski @ X27) @ X28) | ~ (r2_hidden @ X27 @ X28))),
% 0.34/0.52      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.34/0.52  thf('36', plain,
% 0.34/0.52      ((![X0 : $i]: ~ (r2_hidden @ sk_B @ X0))
% 0.34/0.52         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))) & 
% 0.34/0.52             (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.34/0.52  thf('37', plain,
% 0.34/0.52      (~
% 0.34/0.52       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A))) | 
% 0.34/0.52       ~ (((sk_A) = (sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['19', '36'])).
% 0.34/0.52  thf('38', plain,
% 0.34/0.52      (~
% 0.34/0.52       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A))) | 
% 0.34/0.52       (((sk_A) = (sk_B)))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('39', plain,
% 0.34/0.52      (~
% 0.34/0.52       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A)))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['18', '37', '38'])).
% 0.34/0.52  thf('40', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['16', '39'])).
% 0.34/0.52  thf('41', plain,
% 0.34/0.52      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X25 @ X24)
% 0.34/0.52          | (r1_tarski @ X25 @ X23)
% 0.34/0.52          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 0.34/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.34/0.52  thf('42', plain,
% 0.34/0.52      (![X23 : $i, X25 : $i]:
% 0.34/0.52         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.34/0.52  thf('43', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.34/0.52      inference('sup-', [status(thm)], ['40', '42'])).
% 0.34/0.52  thf('44', plain,
% 0.34/0.52      (![X4 : $i, X6 : $i]:
% 0.34/0.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.34/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.34/0.52  thf('45', plain, ((~ (r1_tarski @ sk_A @ sk_B) | ((sk_A) = (sk_B)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['43', '44'])).
% 0.34/0.52  thf('46', plain, ((((sk_A) != (sk_B))) <= (~ (((sk_A) = (sk_B))))),
% 0.34/0.52      inference('split', [status(esa)], ['17'])).
% 0.34/0.52  thf('47', plain, (~ (((sk_A) = (sk_B)))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['18', '37'])).
% 0.34/0.52  thf('48', plain, (((sk_A) != (sk_B))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['46', '47'])).
% 0.34/0.52  thf('49', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.34/0.52      inference('simplify_reflect-', [status(thm)], ['45', '48'])).
% 0.34/0.52  thf('50', plain,
% 0.34/0.52      (![X29 : $i, X30 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.34/0.52      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.34/0.52  thf('51', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('52', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('53', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('54', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X1 @ X0)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.34/0.52          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.34/0.52      inference('sup-', [status(thm)], ['52', '53'])).
% 0.34/0.52  thf('55', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.34/0.52          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.34/0.52          | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['51', '54'])).
% 0.34/0.52  thf('56', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.34/0.52      inference('simplify', [status(thm)], ['55'])).
% 0.34/0.52  thf('57', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['50', '56'])).
% 0.34/0.52  thf('58', plain,
% 0.34/0.52      (![X9 : $i, X10 : $i]:
% 0.34/0.52         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.34/0.52      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.34/0.52  thf('59', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ X0 @ X1)
% 0.34/0.52          | ((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.34/0.52  thf('60', plain,
% 0.34/0.52      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          != (k1_tarski @ sk_A)))
% 0.34/0.52         <= (~
% 0.34/0.52             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52                = (k1_tarski @ sk_A))))),
% 0.34/0.52      inference('split', [status(esa)], ['9'])).
% 0.34/0.52  thf('61', plain,
% 0.34/0.52      (~
% 0.34/0.52       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52          = (k1_tarski @ sk_A)))),
% 0.34/0.52      inference('sat_resolution*', [status(thm)], ['18', '37', '38'])).
% 0.34/0.52  thf('62', plain,
% 0.34/0.52      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.34/0.52         != (k1_tarski @ sk_A))),
% 0.34/0.52      inference('simpl_trail', [status(thm)], ['60', '61'])).
% 0.34/0.52  thf('63', plain,
% 0.34/0.52      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.34/0.52        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['59', '62'])).
% 0.34/0.52  thf('64', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.34/0.52      inference('simplify', [status(thm)], ['63'])).
% 0.34/0.52  thf('65', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['50', '56'])).
% 0.34/0.52  thf('66', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.34/0.52      inference('sup-', [status(thm)], ['1', '3'])).
% 0.34/0.52  thf('67', plain,
% 0.34/0.52      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.34/0.52         (~ (r2_hidden @ X2 @ X0)
% 0.34/0.52          | ~ (r2_hidden @ X2 @ X3)
% 0.34/0.52          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.34/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.34/0.52  thf('68', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         (~ (r1_xboole_0 @ (k1_zfmisc_1 @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.34/0.52      inference('sup-', [status(thm)], ['66', '67'])).
% 0.34/0.52  thf('69', plain,
% 0.34/0.52      (![X0 : $i, X1 : $i]:
% 0.34/0.52         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ X1))
% 0.34/0.52          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.34/0.52      inference('sup-', [status(thm)], ['65', '68'])).
% 0.34/0.52  thf('70', plain, ((r2_hidden @ sk_A @ (k1_zfmisc_1 @ sk_B))),
% 0.34/0.52      inference('sup-', [status(thm)], ['64', '69'])).
% 0.34/0.52  thf('71', plain,
% 0.34/0.52      (![X23 : $i, X25 : $i]:
% 0.34/0.52         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 0.34/0.52      inference('simplify', [status(thm)], ['41'])).
% 0.34/0.52  thf('72', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.34/0.52      inference('sup-', [status(thm)], ['70', '71'])).
% 0.34/0.52  thf('73', plain, ($false), inference('demod', [status(thm)], ['49', '72'])).
% 0.34/0.52  
% 0.34/0.52  % SZS output end Refutation
% 0.34/0.52  
% 0.34/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
