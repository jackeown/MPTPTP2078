%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S8shDAKw5g

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 182 expanded)
%              Number of leaves         :   11 (  54 expanded)
%              Depth                    :   18
%              Number of atoms          :  480 (2346 expanded)
%              Number of equality atoms :    6 (  74 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t8_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                <=> ( r2_hidden @ D @ C ) ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( r2_hidden @ D @ B )
                  <=> ( r2_hidden @ D @ C ) ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ A )
               => ( ( r2_hidden @ D @ B )
                 => ( r2_hidden @ D @ C ) ) )
           => ( r1_tarski @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ X0 )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( ~ ( r2_hidden @ X6 @ sk_C )
      | ( r2_hidden @ X6 @ sk_B )
      | ~ ( m1_subset_1 @ X6 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( sk_D @ sk_B @ sk_C @ sk_A ) @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( r1_tarski @ sk_C @ sk_B )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(simplify,[status(thm)],['19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( sk_B = sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_A )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( m1_subset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X6: $i] :
      ( ~ ( r2_hidden @ X6 @ sk_B )
      | ( r2_hidden @ X6 @ sk_C )
      | ~ ( m1_subset_1 @ X6 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ~ ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ X0 )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('38',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(demod,[status(thm)],['31','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

thf('41',plain,(
    r2_hidden @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( r1_tarski @ X5 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X3 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t7_subset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C @ X0 @ sk_A ) @ sk_C )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['24','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S8shDAKw5g
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:57:40 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 29 iterations in 0.018s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.46  thf(t8_subset_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46           ( ( ![D:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.46                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.46             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46          ( ![C:$i]:
% 0.20/0.46            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46              ( ( ![D:$i]:
% 0.20/0.46                  ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.46                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.46                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t8_subset_1])).
% 0.20/0.46  thf('0', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t7_subset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.46           ( ( ![D:$i]:
% 0.20/0.46               ( ( m1_subset_1 @ D @ A ) =>
% 0.20/0.46                 ( ( r2_hidden @ D @ B ) => ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.46             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.46          | (r1_tarski @ X5 @ X3)
% 0.20/0.46          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.46          | (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ X0)
% 0.20/0.46          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.46        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf('5', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.46          | (r1_tarski @ X5 @ X3)
% 0.20/0.46          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.46          | (m1_subset_1 @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_A)
% 0.20/0.46          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.46        | (m1_subset_1 @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X6 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X6 @ sk_C)
% 0.20/0.46          | (r2_hidden @ X6 @ sk_B)
% 0.20/0.46          | ~ (m1_subset_1 @ X6 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.46        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_B)
% 0.20/0.46        | ~ (r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.46        | (r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_B)
% 0.20/0.46        | (r1_tarski @ sk_C @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (((r2_hidden @ (sk_D @ sk_B @ sk_C @ sk_A) @ sk_B)
% 0.20/0.46        | (r1_tarski @ sk_C @ sk_B))),
% 0.20/0.46      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.46  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.46          | (r1_tarski @ X5 @ X3)
% 0.20/0.46          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.46          | ~ (r2_hidden @ (sk_D @ sk_B @ X0 @ sk_A) @ sk_B)
% 0.20/0.46          | (r1_tarski @ X0 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (((r1_tarski @ sk_C @ sk_B)
% 0.20/0.46        | (r1_tarski @ sk_C @ sk_B)
% 0.20/0.46        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.46  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('19', plain, (((r1_tarski @ sk_C @ sk_B) | (r1_tarski @ sk_C @ sk_B))),
% 0.20/0.46      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.20/0.46      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.46  thf(d10_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X0 : $i, X2 : $i]:
% 0.20/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.46  thf('22', plain, ((~ (r1_tarski @ sk_B @ sk_C) | ((sk_B) = (sk_C)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.46  thf('23', plain, (((sk_B) != (sk_C))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('24', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('26', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.46          | (r1_tarski @ X5 @ X3)
% 0.20/0.46          | (m1_subset_1 @ (sk_D @ X3 @ X5 @ X4) @ X4)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.46          | (m1_subset_1 @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_A)
% 0.20/0.46          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.46        | (m1_subset_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X6 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X6 @ sk_B)
% 0.20/0.46          | (r2_hidden @ X6 @ sk_C)
% 0.20/0.46          | ~ (m1_subset_1 @ X6 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.20/0.46        | ~ (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('33', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('34', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.46          | (r1_tarski @ X5 @ X3)
% 0.20/0.46          | (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X5)
% 0.20/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.46          | (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ X0)
% 0.20/0.46          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['32', '35'])).
% 0.20/0.46  thf('37', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('38', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)),
% 0.20/0.46      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.46        | (r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '38'])).
% 0.20/0.46  thf('40', plain, (~ (r1_tarski @ sk_B @ sk_C)),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('41', plain, ((r2_hidden @ (sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)),
% 0.20/0.46      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.46  thf('42', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('43', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.47          | (r1_tarski @ X5 @ X3)
% 0.20/0.47          | ~ (r2_hidden @ (sk_D @ X3 @ X5 @ X4) @ X3)
% 0.20/0.47          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t7_subset_1])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.47          | ~ (r2_hidden @ (sk_D @ sk_C @ X0 @ sk_A) @ sk_C)
% 0.20/0.47          | (r1_tarski @ X0 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (((r1_tarski @ sk_B @ sk_C)
% 0.20/0.47        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '44'])).
% 0.20/0.47  thf('46', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['45', '46'])).
% 0.20/0.47  thf('48', plain, ($false), inference('demod', [status(thm)], ['24', '47'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
