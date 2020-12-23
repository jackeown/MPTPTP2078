%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b2CNK0TgVq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 (  89 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  448 ( 769 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('5',plain,(
    r2_hidden @ sk_C_2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( r1_tarski @ X10 @ X8 )
      | ( X9
       != ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('7',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r1_tarski @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_C_2 )
      | ( r2_hidden @ X18 @ sk_B )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_2 ) @ sk_B )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,
    ( ( r1_tarski @ sk_C_2 @ sk_B )
    | ( r1_tarski @ sk_C_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(simplify,[status(thm)],['21'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_2 )
    | ( sk_B = sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    sk_B != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ X13 )
      | ( r2_hidden @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('32',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X8: $i,X10: $i] :
      ( ( r1_tarski @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('34',plain,(
    r1_tarski @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( m1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X15: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X18: $i] :
      ( ~ ( r2_hidden @ X18 @ sk_B )
      | ( r2_hidden @ X18 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_2 )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ sk_C_2 )
    | ( r1_tarski @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    r1_tarski @ sk_B @ sk_C_2 ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['26','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b2CNK0TgVq
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:34:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 101 iterations in 0.058s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(t44_setfam_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52       ( ![C:$i]:
% 0.20/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52           ( ( ![D:$i]:
% 0.20/0.52               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52                 ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.52             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52          ( ![C:$i]:
% 0.20/0.52            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.52              ( ( ![D:$i]:
% 0.20/0.52                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52                    ( ( r2_hidden @ D @ B ) <=> ( r2_hidden @ D @ C ) ) ) ) =>
% 0.20/0.52                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t44_setfam_1])).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d2_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.52  thf('2', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X12 @ X13)
% 0.20/0.52          | (r2_hidden @ X12 @ X13)
% 0.20/0.52          | (v1_xboole_0 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.52        | (r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.52  thf(fc1_subset_1, axiom,
% 0.20/0.52    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.52  thf('4', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      ((r2_hidden @ sk_C_2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['3', '4'])).
% 0.20/0.52  thf(d1_zfmisc_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X10 @ X9)
% 0.20/0.52          | (r1_tarski @ X10 @ X8)
% 0.20/0.52          | ((X9) != (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (![X8 : $i, X10 : $i]:
% 0.20/0.52         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('8', plain, ((r1_tarski @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('10', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_C_2 @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '10'])).
% 0.20/0.52  thf('12', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ X13)
% 0.20/0.52          | (m1_subset_1 @ X12 @ X13)
% 0.20/0.52          | (v1_xboole_0 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_C_2 @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | (m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.52  thf('14', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_C @ X0 @ sk_C_2) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | (r1_tarski @ sk_C_2 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['13', '14'])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X18 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X18 @ sk_C_2)
% 0.20/0.52          | (r2_hidden @ X18 @ sk_B)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_C_2 @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B)
% 0.20/0.52          | ~ (r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C @ X0 @ sk_C_2) @ sk_B) | (r1_tarski @ sk_C_2 @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('21', plain,
% 0.20/0.52      (((r1_tarski @ sk_C_2 @ sk_B) | (r1_tarski @ sk_C_2 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.52  thf('22', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 0.20/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.52  thf(d10_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (![X4 : $i, X6 : $i]:
% 0.20/0.52         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.52  thf('24', plain, ((~ (r1_tarski @ sk_B @ sk_C_2) | ((sk_B) = (sk_C_2)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.52  thf('25', plain, (((sk_B) != (sk_C_2))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain, (~ (r1_tarski @ sk_B @ sk_C_2)),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('28', plain,
% 0.20/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (m1_subset_1 @ X12 @ X13)
% 0.20/0.52          | (r2_hidden @ X12 @ X13)
% 0.20/0.52          | (v1_xboole_0 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.52        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('32', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('clc', [status(thm)], ['30', '31'])).
% 0.20/0.52  thf('33', plain,
% 0.20/0.52      (![X8 : $i, X10 : $i]:
% 0.20/0.52         ((r1_tarski @ X10 @ X8) | ~ (r2_hidden @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.20/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.52  thf('34', plain, ((r1_tarski @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.52          | (r2_hidden @ X0 @ X2)
% 0.20/0.52          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '36'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      (![X12 : $i, X13 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X12 @ X13)
% 0.20/0.52          | (m1_subset_1 @ X12 @ X13)
% 0.20/0.52          | (v1_xboole_0 @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B @ X0)
% 0.20/0.52          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain, (![X15 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.20/0.52      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.52          | (r1_tarski @ sk_B @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      (![X18 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X18 @ sk_B)
% 0.20/0.52          | (r2_hidden @ X18 @ sk_C_2)
% 0.20/0.52          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B @ X0)
% 0.20/0.52          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2)
% 0.20/0.52          | ~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B))),
% 0.20/0.52      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('45', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_2) | (r1_tarski @ sk_B @ X0))),
% 0.20/0.52      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X1 : $i, X3 : $i]:
% 0.20/0.52         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (((r1_tarski @ sk_B @ sk_C_2) | (r1_tarski @ sk_B @ sk_C_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.52  thf('48', plain, ((r1_tarski @ sk_B @ sk_C_2)),
% 0.20/0.52      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.52  thf('49', plain, ($false), inference('demod', [status(thm)], ['26', '48'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.33/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
