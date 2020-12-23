%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B6fBacvqEP

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:10 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 210 expanded)
%              Number of leaves         :   23 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :  549 (2017 expanded)
%              Number of equality atoms :   77 ( 295 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t10_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) )
        & ~ ( ( ( k7_setfam_1 @ A @ B )
             != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ~ ( ( B != k1_xboole_0 )
              & ( ( k7_setfam_1 @ A @ B )
                = k1_xboole_0 ) )
          & ~ ( ( ( k7_setfam_1 @ A @ B )
               != k1_xboole_0 )
              & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_tops_2])).

thf('0',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_setfam_1 @ X12 @ ( k7_setfam_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t51_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) )
      | ( r1_tarski @ X26 @ X24 )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X25 @ X26 ) @ ( k7_setfam_1 @ X25 @ X24 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t51_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k7_setfam_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11','14'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_setfam_1 @ X12 @ ( k7_setfam_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('22',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k7_setfam_1 @ sk_A @ k1_xboole_0 )
      = sk_B_1 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( k1_xboole_0 = sk_B_1 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( sk_B_1 = X0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ( ( k7_setfam_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( ( k7_setfam_1 @ sk_A @ X0 )
         != sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k1_xboole_0 != sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('36',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('37',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( sk_B @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ~ ( r2_hidden @ X5 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('44',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
       != k1_xboole_0 )
      & ( sk_B_1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['34','35','36','46'])).

thf('48',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('50',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['25','48','49'])).

thf('51',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(simpl_trail,[status(thm)],['24','50'])).

thf('52',plain,
    ( ( sk_B_1 != sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['1','51'])).

thf('53',plain,
    ( $false
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['25','48'])).

thf('55',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['53','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.B6fBacvqEP
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:37:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 1237 iterations in 0.638s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.10  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.91/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.10  thf(t10_tops_2, conjecture,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.10       ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.91/1.10              ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.10         ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.91/1.10              ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i,B:$i]:
% 0.91/1.10        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.10          ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.91/1.10                 ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.10            ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.91/1.10                 ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t10_tops_2])).
% 0.91/1.10  thf('0', plain,
% 0.91/1.10      ((((sk_B_1) != (k1_xboole_0))
% 0.91/1.10        | ((k7_setfam_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['0'])).
% 0.91/1.10  thf(t4_subset_1, axiom,
% 0.91/1.10    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(involutiveness_k7_setfam_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.10       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i]:
% 0.91/1.10         (((k7_setfam_1 @ X12 @ (k7_setfam_1 @ X12 @ X11)) = (X11))
% 0.91/1.10          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.91/1.10      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(t51_setfam_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.10       ( ![C:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.10           ( ( r1_tarski @ ( k7_setfam_1 @ A @ B ) @ ( k7_setfam_1 @ A @ C ) ) =>
% 0.91/1.10             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25)))
% 0.91/1.10          | (r1_tarski @ X26 @ X24)
% 0.91/1.10          | ~ (r1_tarski @ (k7_setfam_1 @ X25 @ X26) @ 
% 0.91/1.10               (k7_setfam_1 @ X25 @ X24))
% 0.91/1.10          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.91/1.10      inference('cnf', [status(esa)], [t51_setfam_1])).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.91/1.10          | ~ (r1_tarski @ (k7_setfam_1 @ X0 @ X1) @ 
% 0.91/1.10               (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.91/1.10          | (r1_tarski @ X1 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['5', '6'])).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (r1_tarski @ k1_xboole_0 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.91/1.10          | (r1_tarski @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.91/1.10          | ~ (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.91/1.10               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['4', '7'])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(t3_subset, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X15 : $i, X16 : $i]:
% 0.91/1.10         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.10  thf('11', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(dt_k7_setfam_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.91/1.10       ( m1_subset_1 @
% 0.91/1.10         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      (![X9 : $i, X10 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k7_setfam_1 @ X9 @ X10) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9)))
% 0.91/1.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.91/1.10          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (![X0 : $i]: (r1_tarski @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ k1_xboole_0)),
% 0.91/1.10      inference('demod', [status(thm)], ['8', '11', '14'])).
% 0.91/1.10  thf(t3_xboole_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X0 : $i]: ((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.91/1.10        | ((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.91/1.10         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      (![X11 : $i, X12 : $i]:
% 0.91/1.10         (((k7_setfam_1 @ X12 @ (k7_setfam_1 @ X12 @ X11)) = (X11))
% 0.91/1.10          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X12))))),
% 0.91/1.10      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      ((((k7_setfam_1 @ sk_A @ k1_xboole_0) = (sk_B_1)))
% 0.91/1.10         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup+', [status(thm)], ['19', '22'])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      ((((k1_xboole_0) = (sk_B_1)))
% 0.91/1.10         <= ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup+', [status(thm)], ['17', '23'])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (~ (((sk_B_1) = (k1_xboole_0))) | 
% 0.91/1.10       ~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('split', [status(esa)], ['0'])).
% 0.91/1.10  thf('26', plain,
% 0.91/1.10      (![X0 : $i]: ((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['15', '16'])).
% 0.91/1.10  thf(l13_xboole_0, axiom,
% 0.91/1.10    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.10      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      ((![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0)))
% 0.91/1.10         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup+', [status(thm)], ['27', '28'])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      ((((k7_setfam_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.91/1.10         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['0'])).
% 0.91/1.10  thf('31', plain,
% 0.91/1.10      ((![X0 : $i]:
% 0.91/1.10          (((k7_setfam_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.91/1.10         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.91/1.10             (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      ((![X0 : $i]:
% 0.91/1.10          (((k7_setfam_1 @ sk_A @ X0) != (sk_B_1)) | ~ (v1_xboole_0 @ X0)))
% 0.91/1.10         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.91/1.10             (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['31', '32'])).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (((((k1_xboole_0) != (sk_B_1)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.91/1.10         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.91/1.10             (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['26', '33'])).
% 0.91/1.10  thf('35', plain,
% 0.91/1.10      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf('36', plain,
% 0.91/1.10      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf(existence_m1_subset_1, axiom,
% 0.91/1.10    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.91/1.10  thf('37', plain, (![X7 : $i]: (m1_subset_1 @ (sk_B @ X7) @ X7)),
% 0.91/1.10      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.91/1.10  thf(t2_subset, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ A @ B ) =>
% 0.91/1.10       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.91/1.10  thf('38', plain,
% 0.91/1.10      (![X13 : $i, X14 : $i]:
% 0.91/1.10         ((r2_hidden @ X13 @ X14)
% 0.91/1.10          | (v1_xboole_0 @ X14)
% 0.91/1.10          | ~ (m1_subset_1 @ X13 @ X14))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_subset])).
% 0.91/1.10  thf('39', plain,
% 0.91/1.10      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.10  thf('40', plain,
% 0.91/1.10      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf(t113_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.10       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.10  thf('41', plain,
% 0.91/1.10      (![X3 : $i, X4 : $i]:
% 0.91/1.10         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.10  thf('42', plain,
% 0.91/1.10      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.10      inference('simplify', [status(thm)], ['41'])).
% 0.91/1.10  thf(t152_zfmisc_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.91/1.10  thf('43', plain,
% 0.91/1.10      (![X5 : $i, X6 : $i]: ~ (r2_hidden @ X5 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.91/1.10      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.91/1.10  thf('44', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.91/1.10      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.10  thf('45', plain,
% 0.91/1.10      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_1))
% 0.91/1.10         <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['40', '44'])).
% 0.91/1.10  thf('46', plain,
% 0.91/1.10      (((v1_xboole_0 @ sk_B_1)) <= ((((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['39', '45'])).
% 0.91/1.10  thf('47', plain,
% 0.91/1.10      ((((sk_B_1) != (sk_B_1)))
% 0.91/1.10         <= (~ (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) & 
% 0.91/1.10             (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['34', '35', '36', '46'])).
% 0.91/1.10  thf('48', plain,
% 0.91/1.10      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.91/1.10       ~ (((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['47'])).
% 0.91/1.10  thf('49', plain,
% 0.91/1.10      ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.91/1.10       (((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('split', [status(esa)], ['18'])).
% 0.91/1.10  thf('50', plain, ((((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('sat_resolution*', [status(thm)], ['25', '48', '49'])).
% 0.91/1.10  thf('51', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.91/1.10      inference('simpl_trail', [status(thm)], ['24', '50'])).
% 0.91/1.10  thf('52', plain,
% 0.91/1.10      ((((sk_B_1) != (sk_B_1))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['1', '51'])).
% 0.91/1.10  thf('53', plain, (($false) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['52'])).
% 0.91/1.10  thf('54', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('sat_resolution*', [status(thm)], ['25', '48'])).
% 0.91/1.10  thf('55', plain, ($false),
% 0.91/1.10      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
