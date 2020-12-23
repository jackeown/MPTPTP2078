%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.avLADm8tSe

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:08 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 322 expanded)
%              Number of leaves         :   20 ( 105 expanded)
%              Depth                    :   26
%              Number of atoms          :  530 (3055 expanded)
%              Number of equality atoms :   25 (  93 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t44_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_setfam_1])).

thf('0',plain,(
    sk_B_2 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('9',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_C_2 )
      | ( r2_hidden @ X17 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_B_2 )
    | ~ ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_B_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_C_2 )
      | ( r2_hidden @ X17 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_2 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_2 )
    | ( r1_tarski @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ sk_C_2 @ sk_B_2 ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X14: $i,X16: $i] :
      ( ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X8 @ X9 ) @ X9 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('31',plain,
    ( ( sk_B_2 = sk_C_2 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    sk_B_2 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_tarski @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('39',plain,(
    r1_tarski @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_B_2 )
      | ( r2_hidden @ X17 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( sk_B_2 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2 = sk_C_2 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B_2 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','55'])).

thf('57',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','56'])).

thf('58',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['57','62'])).

thf('64',plain,(
    $false ),
    inference(simplify,[status(thm)],['63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.avLADm8tSe
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:03:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.56/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.56/0.74  % Solved by: fo/fo7.sh
% 0.56/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.74  % done 487 iterations in 0.285s
% 0.56/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.56/0.74  % SZS output start Refutation
% 0.56/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.74  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.56/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.56/0.74  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.56/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.74  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.56/0.74  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.56/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.74  thf(t44_setfam_1, conjecture,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.74       ( ![C:$i]:
% 0.56/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.74           ( ( ![D:$i]:
% 0.56/0.74               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.74                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.56/0.74             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.56/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.74    (~( ![A:$i,B:$i]:
% 0.56/0.74        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.74          ( ![C:$i]:
% 0.56/0.74            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.56/0.74              ( ( ![D:$i]:
% 0.56/0.74                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.74                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.56/0.74                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.56/0.74    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.56/0.74  thf('0', plain, (((sk_B_2) != (sk_C_2))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(t7_xboole_0, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.56/0.74          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.56/0.74  thf('1', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.56/0.74  thf('2', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf(t3_subset, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.74  thf('3', plain,
% 0.56/0.74      (![X14 : $i, X15 : $i]:
% 0.56/0.74         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.74  thf('4', plain, ((r1_tarski @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.74  thf(d3_tarski, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( r1_tarski @ A @ B ) <=>
% 0.56/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.56/0.74  thf('5', plain,
% 0.56/0.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X3 @ X4)
% 0.56/0.74          | (r2_hidden @ X3 @ X5)
% 0.56/0.74          | ~ (r1_tarski @ X4 @ X5))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf('6', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.74  thf('7', plain,
% 0.56/0.74      ((((sk_C_2) = (k1_xboole_0))
% 0.56/0.74        | (r2_hidden @ (sk_B_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['1', '6'])).
% 0.56/0.74  thf(t1_subset, axiom,
% 0.56/0.74    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.56/0.74  thf('8', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.56/0.74  thf('9', plain,
% 0.56/0.74      ((((sk_C_2) = (k1_xboole_0))
% 0.56/0.74        | (m1_subset_1 @ (sk_B_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['7', '8'])).
% 0.56/0.74  thf('10', plain,
% 0.56/0.74      (![X17 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X17 @ sk_C_2)
% 0.56/0.74          | (r2_hidden @ X17 @ sk_B_2)
% 0.56/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('11', plain,
% 0.56/0.74      ((((sk_C_2) = (k1_xboole_0))
% 0.56/0.74        | (r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_B_2)
% 0.56/0.74        | ~ (r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_C_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.56/0.74  thf('12', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.56/0.74  thf('13', plain,
% 0.56/0.74      (((r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_B_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.56/0.74      inference('clc', [status(thm)], ['11', '12'])).
% 0.56/0.74  thf(d1_xboole_0, axiom,
% 0.56/0.74    (![A:$i]:
% 0.56/0.74     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.74  thf('14', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.74  thf('15', plain, ((((sk_C_2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.56/0.74  thf('16', plain,
% 0.56/0.74      (![X4 : $i, X6 : $i]:
% 0.56/0.74         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf('17', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['4', '5'])).
% 0.56/0.74  thf('18', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r1_tarski @ sk_C_2 @ X0)
% 0.56/0.74          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['16', '17'])).
% 0.56/0.74  thf('19', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.56/0.74  thf('20', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r1_tarski @ sk_C_2 @ X0)
% 0.56/0.74          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['18', '19'])).
% 0.56/0.74  thf('21', plain,
% 0.56/0.74      (![X17 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X17 @ sk_C_2)
% 0.56/0.74          | (r2_hidden @ X17 @ sk_B_2)
% 0.56/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('22', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r1_tarski @ sk_C_2 @ X0)
% 0.56/0.74          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_2)
% 0.56/0.74          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['20', '21'])).
% 0.56/0.74  thf('23', plain,
% 0.56/0.74      (![X4 : $i, X6 : $i]:
% 0.56/0.74         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf('24', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_2)
% 0.56/0.74          | (r1_tarski @ sk_C_2 @ X0))),
% 0.56/0.74      inference('clc', [status(thm)], ['22', '23'])).
% 0.56/0.74  thf('25', plain,
% 0.56/0.74      (![X4 : $i, X6 : $i]:
% 0.56/0.74         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf('26', plain,
% 0.56/0.74      (((r1_tarski @ sk_C_2 @ sk_B_2) | (r1_tarski @ sk_C_2 @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.56/0.74  thf('27', plain, ((r1_tarski @ sk_C_2 @ sk_B_2)),
% 0.56/0.74      inference('simplify', [status(thm)], ['26'])).
% 0.56/0.74  thf('28', plain,
% 0.56/0.74      (![X14 : $i, X16 : $i]:
% 0.56/0.74         ((m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X16)) | ~ (r1_tarski @ X14 @ X16))),
% 0.56/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.74  thf('29', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf(t49_subset_1, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.56/0.74       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.56/0.74         ( ( A ) = ( B ) ) ) ))).
% 0.56/0.74  thf('30', plain,
% 0.56/0.74      (![X8 : $i, X9 : $i]:
% 0.56/0.74         ((m1_subset_1 @ (sk_C_1 @ X8 @ X9) @ X9)
% 0.56/0.74          | ((X9) = (X8))
% 0.56/0.74          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.56/0.74  thf('31', plain,
% 0.56/0.74      ((((sk_B_2) = (sk_C_2))
% 0.56/0.74        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['29', '30'])).
% 0.56/0.74  thf('32', plain, (((sk_B_2) != (sk_C_2))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('33', plain, ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2)),
% 0.56/0.74      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.56/0.74  thf(t2_subset, axiom,
% 0.56/0.74    (![A:$i,B:$i]:
% 0.56/0.74     ( ( m1_subset_1 @ A @ B ) =>
% 0.56/0.74       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.56/0.74  thf('34', plain,
% 0.56/0.74      (![X12 : $i, X13 : $i]:
% 0.56/0.74         ((r2_hidden @ X12 @ X13)
% 0.56/0.74          | (v1_xboole_0 @ X13)
% 0.56/0.74          | ~ (m1_subset_1 @ X12 @ X13))),
% 0.56/0.74      inference('cnf', [status(esa)], [t2_subset])).
% 0.56/0.74  thf('35', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.56/0.74  thf('36', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['33', '34'])).
% 0.56/0.74  thf('37', plain,
% 0.56/0.74      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('38', plain,
% 0.56/0.74      (![X14 : $i, X15 : $i]:
% 0.56/0.74         ((r1_tarski @ X14 @ X15) | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.74  thf('39', plain, ((r1_tarski @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.56/0.74      inference('sup-', [status(thm)], ['37', '38'])).
% 0.56/0.74  thf('40', plain,
% 0.56/0.74      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X3 @ X4)
% 0.56/0.74          | (r2_hidden @ X3 @ X5)
% 0.56/0.74          | ~ (r1_tarski @ X4 @ X5))),
% 0.56/0.74      inference('cnf', [status(esa)], [d3_tarski])).
% 0.56/0.74  thf('41', plain,
% 0.56/0.74      (![X0 : $i]:
% 0.56/0.74         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['39', '40'])).
% 0.56/0.74  thf('42', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['36', '41'])).
% 0.56/0.74  thf('43', plain,
% 0.56/0.74      (![X10 : $i, X11 : $i]:
% 0.56/0.74         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 0.56/0.74      inference('cnf', [status(esa)], [t1_subset])).
% 0.56/0.74  thf('44', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['42', '43'])).
% 0.56/0.74  thf('45', plain,
% 0.56/0.74      (![X17 : $i]:
% 0.56/0.74         (~ (r2_hidden @ X17 @ sk_B_2)
% 0.56/0.74          | (r2_hidden @ X17 @ sk_C_2)
% 0.56/0.74          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ sk_A)))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('46', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_C_2)
% 0.56/0.74        | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['44', '45'])).
% 0.56/0.74  thf('47', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.74  thf('48', plain,
% 0.56/0.74      ((~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2)
% 0.56/0.74        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_C_2))),
% 0.56/0.74      inference('clc', [status(thm)], ['46', '47'])).
% 0.56/0.74  thf('49', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_C_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['35', '48'])).
% 0.56/0.74  thf('50', plain,
% 0.56/0.74      (![X8 : $i, X9 : $i]:
% 0.56/0.74         (~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.56/0.74          | ((X9) = (X8))
% 0.56/0.74          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.56/0.74      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.56/0.74  thf('51', plain,
% 0.56/0.74      (((v1_xboole_0 @ sk_B_2)
% 0.56/0.74        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_2))
% 0.56/0.74        | ((sk_B_2) = (sk_C_2)))),
% 0.56/0.74      inference('sup-', [status(thm)], ['49', '50'])).
% 0.56/0.74  thf('52', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.56/0.74      inference('sup-', [status(thm)], ['27', '28'])).
% 0.56/0.74  thf('53', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_B_2) = (sk_C_2)))),
% 0.56/0.74      inference('demod', [status(thm)], ['51', '52'])).
% 0.56/0.74  thf('54', plain, (((sk_B_2) != (sk_C_2))),
% 0.56/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.74  thf('55', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.56/0.74      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.56/0.74  thf('56', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['15', '55'])).
% 0.56/0.74  thf('57', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['0', '56'])).
% 0.56/0.74  thf('58', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.56/0.74      inference('simplify_reflect-', [status(thm)], ['53', '54'])).
% 0.56/0.74  thf('59', plain,
% 0.56/0.74      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.56/0.74      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.56/0.74  thf('60', plain,
% 0.56/0.74      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.74      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.74  thf('61', plain,
% 0.56/0.74      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['59', '60'])).
% 0.56/0.74  thf('62', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.56/0.74      inference('sup-', [status(thm)], ['58', '61'])).
% 0.56/0.74  thf('63', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.56/0.74      inference('demod', [status(thm)], ['57', '62'])).
% 0.56/0.74  thf('64', plain, ($false), inference('simplify', [status(thm)], ['63'])).
% 0.56/0.74  
% 0.56/0.74  % SZS output end Refutation
% 0.56/0.74  
% 0.56/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
