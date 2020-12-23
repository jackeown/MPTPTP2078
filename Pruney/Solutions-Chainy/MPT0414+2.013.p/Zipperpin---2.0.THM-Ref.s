%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vfqdxGoSSb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:08 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 378 expanded)
%              Number of leaves         :   19 ( 121 expanded)
%              Depth                    :   24
%              Number of atoms          :  551 (3501 expanded)
%              Number of equality atoms :   15 (  81 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

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

thf('2',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
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
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( m1_subset_1 @ ( sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_2 )
      | ( r2_hidden @ X19 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,
    ( ~ ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_C_2 )
      | ( r2_hidden @ X19 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_1 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_1 )
    | ( r1_tarski @ sk_C_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X13: $i,X15: $i] :
      ( ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X9 @ X10 ) @ X10 )
      | ( X10 = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('39',plain,
    ( ( sk_B_1 = sk_C_2 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ X12 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('45',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X18 ) )
      | ( m1_subset_1 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X19: $i] :
      ( ~ ( r2_hidden @ X19 @ sk_B_1 )
      | ( r2_hidden @ X19 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( X10 = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('55',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( sk_B_1 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('57',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1 = sk_C_2 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_xboole_0 @ sk_C_2 ),
    inference(demod,[status(thm)],['23','59'])).

thf('61',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('62',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    sk_B_1 = sk_C_2 ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vfqdxGoSSb
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.69  % Solved by: fo/fo7.sh
% 0.49/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.69  % done 288 iterations in 0.237s
% 0.49/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.69  % SZS output start Refutation
% 0.49/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.49/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.69  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.49/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.49/0.69  thf(d1_xboole_0, axiom,
% 0.49/0.69    (![A:$i]:
% 0.49/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.69  thf('0', plain,
% 0.49/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.69  thf('1', plain,
% 0.49/0.69      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.69  thf(t44_setfam_1, conjecture,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.69       ( ![C:$i]:
% 0.49/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.69           ( ( ![D:$i]:
% 0.49/0.69               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.49/0.69             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.49/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.69    (~( ![A:$i,B:$i]:
% 0.49/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.69          ( ![C:$i]:
% 0.49/0.69            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.49/0.69              ( ( ![D:$i]:
% 0.49/0.69                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.49/0.69                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.49/0.69    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.49/0.69  thf('2', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf(t3_subset, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.49/0.69  thf('3', plain,
% 0.49/0.69      (![X13 : $i, X14 : $i]:
% 0.49/0.69         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.69  thf('4', plain, ((r1_tarski @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.49/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.69  thf(d3_tarski, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.49/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.49/0.69  thf('5', plain,
% 0.49/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X3 @ X4)
% 0.49/0.69          | (r2_hidden @ X3 @ X5)
% 0.49/0.69          | ~ (r1_tarski @ X4 @ X5))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.69  thf('6', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.69  thf('7', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_C_2)
% 0.49/0.69        | (r2_hidden @ (sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['1', '6'])).
% 0.49/0.69  thf('8', plain,
% 0.49/0.69      (![X4 : $i, X6 : $i]:
% 0.49/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.69  thf('9', plain,
% 0.49/0.69      (![X4 : $i, X6 : $i]:
% 0.49/0.69         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.69  thf('10', plain,
% 0.49/0.69      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.69  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.49/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.49/0.69  thf('12', plain,
% 0.49/0.69      (![X13 : $i, X15 : $i]:
% 0.49/0.69         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.69  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.69  thf(t4_subset, axiom,
% 0.49/0.69    (![A:$i,B:$i,C:$i]:
% 0.49/0.69     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.49/0.69       ( m1_subset_1 @ A @ C ) ))).
% 0.49/0.69  thf('14', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X16 @ X17)
% 0.49/0.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.49/0.69          | (m1_subset_1 @ X16 @ X18))),
% 0.49/0.69      inference('cnf', [status(esa)], [t4_subset])).
% 0.49/0.69  thf('15', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.69  thf('16', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_C_2)
% 0.49/0.69        | (m1_subset_1 @ (sk_B @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['7', '15'])).
% 0.49/0.69  thf('17', plain,
% 0.49/0.69      (![X19 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X19 @ sk_C_2)
% 0.49/0.69          | (r2_hidden @ X19 @ sk_B_1)
% 0.49/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('18', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_C_2)
% 0.49/0.69        | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)
% 0.49/0.69        | ~ (r2_hidden @ (sk_B @ sk_C_2) @ sk_C_2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.69  thf('19', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.69  thf('20', plain,
% 0.49/0.69      ((~ (r2_hidden @ (sk_B @ sk_C_2) @ sk_C_2)
% 0.49/0.69        | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1))),
% 0.49/0.69      inference('clc', [status(thm)], ['18', '19'])).
% 0.49/0.69  thf('21', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_C_2) | (r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['0', '20'])).
% 0.49/0.69  thf('22', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.69  thf('23', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.69  thf('24', plain,
% 0.49/0.69      (![X4 : $i, X6 : $i]:
% 0.49/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.69  thf('25', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.69  thf('26', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r1_tarski @ sk_C_2 @ X0)
% 0.49/0.69          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.49/0.69  thf('27', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.69  thf('28', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r1_tarski @ sk_C_2 @ X0)
% 0.49/0.69          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.69  thf('29', plain,
% 0.49/0.69      (![X19 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X19 @ sk_C_2)
% 0.49/0.69          | (r2_hidden @ X19 @ sk_B_1)
% 0.49/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('30', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r1_tarski @ sk_C_2 @ X0)
% 0.49/0.69          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 0.49/0.69          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['28', '29'])).
% 0.49/0.69  thf('31', plain,
% 0.49/0.69      (![X4 : $i, X6 : $i]:
% 0.49/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.69  thf('32', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_1)
% 0.49/0.69          | (r1_tarski @ sk_C_2 @ X0))),
% 0.49/0.69      inference('clc', [status(thm)], ['30', '31'])).
% 0.49/0.69  thf('33', plain,
% 0.49/0.69      (![X4 : $i, X6 : $i]:
% 0.49/0.69         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.49/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.49/0.69  thf('34', plain,
% 0.49/0.69      (((r1_tarski @ sk_C_2 @ sk_B_1) | (r1_tarski @ sk_C_2 @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.49/0.69  thf('35', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 0.49/0.69      inference('simplify', [status(thm)], ['34'])).
% 0.49/0.69  thf('36', plain,
% 0.49/0.69      (![X13 : $i, X15 : $i]:
% 0.49/0.69         ((m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X15)) | ~ (r1_tarski @ X13 @ X15))),
% 0.49/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.49/0.69  thf('37', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.69  thf(t49_subset_1, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.49/0.69       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.49/0.69         ( ( A ) = ( B ) ) ) ))).
% 0.49/0.69  thf('38', plain,
% 0.49/0.69      (![X9 : $i, X10 : $i]:
% 0.49/0.69         ((m1_subset_1 @ (sk_C_1 @ X9 @ X10) @ X10)
% 0.49/0.69          | ((X10) = (X9))
% 0.49/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.49/0.69  thf('39', plain,
% 0.49/0.69      ((((sk_B_1) = (sk_C_2))
% 0.49/0.69        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.69  thf('40', plain, (((sk_B_1) != (sk_C_2))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('41', plain, ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1)),
% 0.49/0.69      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.49/0.69  thf(t2_subset, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ( m1_subset_1 @ A @ B ) =>
% 0.49/0.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.49/0.69  thf('42', plain,
% 0.49/0.69      (![X11 : $i, X12 : $i]:
% 0.49/0.69         ((r2_hidden @ X11 @ X12)
% 0.49/0.69          | (v1_xboole_0 @ X12)
% 0.49/0.69          | ~ (m1_subset_1 @ X11 @ X12))),
% 0.49/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.49/0.69  thf('43', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.49/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('44', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.49/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.69  thf('45', plain,
% 0.49/0.69      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('46', plain,
% 0.49/0.69      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X16 @ X17)
% 0.49/0.69          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X18))
% 0.49/0.69          | (m1_subset_1 @ X16 @ X18))),
% 0.49/0.69      inference('cnf', [status(esa)], [t4_subset])).
% 0.49/0.69  thf('47', plain,
% 0.49/0.69      (![X0 : $i]:
% 0.49/0.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.49/0.69          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.69  thf('48', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.49/0.69        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['44', '47'])).
% 0.49/0.69  thf('49', plain,
% 0.49/0.69      (![X19 : $i]:
% 0.49/0.69         (~ (r2_hidden @ X19 @ sk_B_1)
% 0.49/0.69          | (r2_hidden @ X19 @ sk_C_2)
% 0.49/0.69          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ sk_A)))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('50', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.49/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_C_2)
% 0.49/0.69        | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.69  thf('51', plain,
% 0.49/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.69  thf('52', plain,
% 0.49/0.69      ((~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_B_1)
% 0.49/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_C_2))),
% 0.49/0.69      inference('clc', [status(thm)], ['50', '51'])).
% 0.49/0.69  thf('53', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.49/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_1) @ sk_C_2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['43', '52'])).
% 0.49/0.69  thf('54', plain,
% 0.49/0.69      (![X9 : $i, X10 : $i]:
% 0.49/0.69         (~ (r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 0.49/0.69          | ((X10) = (X9))
% 0.49/0.69          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.49/0.69  thf('55', plain,
% 0.49/0.69      (((v1_xboole_0 @ sk_B_1)
% 0.49/0.69        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_1))
% 0.49/0.69        | ((sk_B_1) = (sk_C_2)))),
% 0.49/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.69  thf('56', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_1))),
% 0.49/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.69  thf('57', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (sk_C_2)))),
% 0.49/0.69      inference('demod', [status(thm)], ['55', '56'])).
% 0.49/0.69  thf('58', plain, (((sk_B_1) != (sk_C_2))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('59', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.49/0.69      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.49/0.69  thf('60', plain, ((v1_xboole_0 @ sk_C_2)),
% 0.49/0.69      inference('demod', [status(thm)], ['23', '59'])).
% 0.49/0.69  thf('61', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.49/0.69      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.49/0.69  thf(t8_boole, axiom,
% 0.49/0.69    (![A:$i,B:$i]:
% 0.49/0.69     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.49/0.69  thf('62', plain,
% 0.49/0.69      (![X7 : $i, X8 : $i]:
% 0.49/0.69         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.49/0.69      inference('cnf', [status(esa)], [t8_boole])).
% 0.49/0.69  thf('63', plain, (![X0 : $i]: (((sk_B_1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.69      inference('sup-', [status(thm)], ['61', '62'])).
% 0.49/0.69  thf('64', plain, (((sk_B_1) = (sk_C_2))),
% 0.49/0.69      inference('sup-', [status(thm)], ['60', '63'])).
% 0.49/0.69  thf('65', plain, (((sk_B_1) != (sk_C_2))),
% 0.49/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.69  thf('66', plain, ($false),
% 0.49/0.69      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.49/0.69  
% 0.49/0.69  % SZS output end Refutation
% 0.49/0.69  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
