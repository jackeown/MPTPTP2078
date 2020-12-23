%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gzb7XnlhZp

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:08 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 268 expanded)
%              Number of leaves         :   20 (  87 expanded)
%              Depth                    :   23
%              Number of atoms          :  471 (2725 expanded)
%              Number of equality atoms :   24 (  92 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('3',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_2 )
      | ( r2_hidden @ X18 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_B_2 )
    | ~ ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_B_1 @ sk_C_2 ) @ sk_B_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('11',plain,
    ( ( sk_C_2 = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_2 )
      | ( r2_hidden @ X18 @ sk_B_2 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B_2 )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B_2 )
    | ( r1_tarski @ sk_C_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_C_2 @ sk_B_2 ),
    inference(simplify,[status(thm)],['20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X8 @ X9 ) @ X9 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('25',plain,
    ( ( sk_B_2 = sk_C_2 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_B_2 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['25','26'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('31',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( m1_subset_1 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B_2 )
      | ( r2_hidden @ X18 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_C_2 )
    | ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,
    ( ~ ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( r2_hidden @ ( sk_C_1 @ sk_C_2 @ sk_B_2 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( X9 = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) )
    | ( sk_B_2 = sk_C_2 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_B_2 = sk_C_2 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    sk_B_2 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(demod,[status(thm)],['11','45'])).

thf('47',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','46'])).

thf('48',plain,(
    v1_xboole_0 @ sk_B_2 ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('49',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['47','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Gzb7XnlhZp
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:03:04 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 485 iterations in 0.255s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.46/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.69  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.46/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.69  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.46/0.69  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(t44_setfam_1, conjecture,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.69       ( ![C:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.69           ( ( ![D:$i]:
% 0.46/0.69               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.46/0.69             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i,B:$i]:
% 0.46/0.69        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.69          ( ![C:$i]:
% 0.46/0.69            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.69              ( ( ![D:$i]:
% 0.46/0.69                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.46/0.69                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.46/0.69  thf('0', plain, (((sk_B_2) != (sk_C_2))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t7_xboole_0, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.69          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t4_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.69       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X15 @ X16)
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.46/0.69          | (m1_subset_1 @ X15 @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      ((((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | (m1_subset_1 @ (sk_B_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['1', '4'])).
% 0.46/0.69  thf('6', plain,
% 0.46/0.69      (![X18 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X18 @ sk_C_2)
% 0.46/0.69          | (r2_hidden @ X18 @ sk_B_2)
% 0.46/0.69          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('7', plain,
% 0.46/0.69      ((((sk_C_2) = (k1_xboole_0))
% 0.46/0.69        | (r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_B_2)
% 0.46/0.69        | ~ (r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (((r2_hidden @ (sk_B_1 @ sk_C_2) @ sk_B_2) | ((sk_C_2) = (k1_xboole_0)))),
% 0.46/0.69      inference('clc', [status(thm)], ['7', '8'])).
% 0.46/0.69  thf(d1_xboole_0, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('11', plain, ((((sk_C_2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.69  thf(d3_tarski, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.46/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X4 : $i, X6 : $i]:
% 0.46/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69          | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r1_tarski @ sk_C_2 @ X0)
% 0.46/0.69          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['12', '13'])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (![X18 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X18 @ sk_C_2)
% 0.46/0.69          | (r2_hidden @ X18 @ sk_B_2)
% 0.46/0.69          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r1_tarski @ sk_C_2 @ X0)
% 0.46/0.69          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_2)
% 0.46/0.69          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (![X4 : $i, X6 : $i]:
% 0.46/0.69         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B_2)
% 0.46/0.69          | (r1_tarski @ sk_C_2 @ X0))),
% 0.46/0.69      inference('clc', [status(thm)], ['16', '17'])).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      (![X4 : $i, X6 : $i]:
% 0.46/0.69         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.46/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      (((r1_tarski @ sk_C_2 @ sk_B_2) | (r1_tarski @ sk_C_2 @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.69  thf('21', plain, ((r1_tarski @ sk_C_2 @ sk_B_2)),
% 0.46/0.69      inference('simplify', [status(thm)], ['20'])).
% 0.46/0.69  thf(t3_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X12 : $i, X14 : $i]:
% 0.46/0.69         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.69  thf('23', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf(t49_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.46/0.69         ( ( A ) = ( B ) ) ) ))).
% 0.46/0.69  thf('24', plain,
% 0.46/0.69      (![X8 : $i, X9 : $i]:
% 0.46/0.69         ((m1_subset_1 @ (sk_C_1 @ X8 @ X9) @ X9)
% 0.46/0.69          | ((X9) = (X8))
% 0.46/0.69          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      ((((sk_B_2) = (sk_C_2))
% 0.46/0.69        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['23', '24'])).
% 0.46/0.69  thf('26', plain, (((sk_B_2) != (sk_C_2))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('27', plain, ((m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2)),
% 0.46/0.69      inference('simplify_reflect-', [status(thm)], ['25', '26'])).
% 0.46/0.69  thf(t2_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.69       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (![X10 : $i, X11 : $i]:
% 0.46/0.69         ((r2_hidden @ X10 @ X11)
% 0.46/0.69          | (v1_xboole_0 @ X11)
% 0.46/0.69          | ~ (m1_subset_1 @ X10 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('30', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('31', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X15 @ X16)
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.46/0.69          | (m1_subset_1 @ X15 @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.69          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.69        | (m1_subset_1 @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['30', '33'])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (![X18 : $i]:
% 0.46/0.69         (~ (r2_hidden @ X18 @ sk_B_2)
% 0.46/0.69          | (r2_hidden @ X18 @ sk_C_2)
% 0.46/0.69          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_C_2)
% 0.46/0.69        | ~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      ((~ (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_B_2)
% 0.46/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_C_2))),
% 0.46/0.69      inference('clc', [status(thm)], ['36', '37'])).
% 0.46/0.69  thf('39', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.69        | (r2_hidden @ (sk_C_1 @ sk_C_2 @ sk_B_2) @ sk_C_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['29', '38'])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (![X8 : $i, X9 : $i]:
% 0.46/0.69         (~ (r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 0.46/0.69          | ((X9) = (X8))
% 0.46/0.69          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.46/0.69  thf('41', plain,
% 0.46/0.69      (((v1_xboole_0 @ sk_B_2)
% 0.46/0.69        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_2))
% 0.46/0.69        | ((sk_B_2) = (sk_C_2)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.69  thf('42', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_B_2))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('43', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_B_2) = (sk_C_2)))),
% 0.46/0.69      inference('demod', [status(thm)], ['41', '42'])).
% 0.46/0.69  thf('44', plain, (((sk_B_2) != (sk_C_2))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('45', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.46/0.69      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.46/0.69  thf('46', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['11', '45'])).
% 0.46/0.69  thf('47', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['0', '46'])).
% 0.46/0.69  thf('48', plain, ((v1_xboole_0 @ sk_B_2)),
% 0.46/0.69      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.46/0.69      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.69  thf('50', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.69      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.69  thf('51', plain,
% 0.46/0.69      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['49', '50'])).
% 0.46/0.69  thf('52', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['48', '51'])).
% 0.46/0.69  thf('53', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.46/0.69      inference('demod', [status(thm)], ['47', '52'])).
% 0.46/0.69  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
