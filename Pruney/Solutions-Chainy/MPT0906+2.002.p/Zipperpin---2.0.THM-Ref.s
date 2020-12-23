%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EDVt3BEVHV

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 159 expanded)
%              Number of leaves         :   17 (  53 expanded)
%              Depth                    :   18
%              Number of atoms          :  407 (1235 expanded)
%              Number of equality atoms :   58 ( 160 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t66_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
       != k1_xboole_0 )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
         => ( ( C
             != ( k1_mcart_1 @ C ) )
            & ( C
             != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k2_zfmisc_1 @ A @ B )
         != k1_xboole_0 )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
           => ( ( C
               != ( k1_mcart_1 @ C ) )
              & ( C
               != ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X9 ) @ X10 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('6',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('11',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_C ) @ sk_A ),
    inference(clc,[status(thm)],['4','12'])).

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

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( ( C
                 != ( k1_mcart_1 @ C ) )
                & ( C
                 != ( k2_mcart_1 @ C ) ) ) ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13
       != ( k1_mcart_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k2_zfmisc_1 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('18',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C
     != ( k1_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k1_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('21',plain,
    ( ( sk_C
      = ( k2_mcart_1 @ sk_C ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( X13
       != ( k2_mcart_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k2_zfmisc_1 @ X12 @ X14 ) )
      | ( X14 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t26_mcart_1])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C
     != ( k2_mcart_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_C != sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( sk_B_1 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X9 ) @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_mcart_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['10','11'])).

thf('31',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_C ) @ sk_B_1 ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('38',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    sk_C
 != ( k2_mcart_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_C
      = ( k1_mcart_1 @ sk_C ) )
    | ( sk_C
      = ( k2_mcart_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['19'])).

thf('42',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_C
    = ( k1_mcart_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['20','42'])).

thf('44',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_C != sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('47',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['15','49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EDVt3BEVHV
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 86 iterations in 0.054s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(t66_mcart_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.51           ( ( ( C ) != ( k1_mcart_1 @ C ) ) & ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( ( k2_zfmisc_1 @ A @ B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.51              ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.51                ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t66_mcart_1])).
% 0.20/0.51  thf('0', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t2_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i]:
% 0.20/0.51         ((r2_hidden @ X5 @ X6)
% 0.20/0.51          | (v1_xboole_0 @ X6)
% 0.20/0.51          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.20/0.51        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf(t10_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.51       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.51         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ (k1_mcart_1 @ X9) @ X10)
% 0.20/0.51          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.20/0.51        | (r2_hidden @ (k1_mcart_1 @ sk_C) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '6'])).
% 0.20/0.51  thf('8', plain, (((k2_zfmisc_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((X0) != (k1_xboole_0))
% 0.20/0.51          | ~ (v1_xboole_0 @ X0)
% 0.20/0.51          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.20/0.51        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.51      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.51  thf('11', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('12', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('simplify_reflect+', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, ((r2_hidden @ (k1_mcart_1 @ sk_C) @ sk_A)),
% 0.20/0.51      inference('clc', [status(thm)], ['4', '12'])).
% 0.20/0.51  thf(d1_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('16', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t26_mcart_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51          ( ~( ![C:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.20/0.51                 ( ( ( C ) != ( k1_mcart_1 @ C ) ) & 
% 0.20/0.51                   ( ( C ) != ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) = (k1_xboole_0))
% 0.20/0.51          | ((X13) != (k1_mcart_1 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k2_zfmisc_1 @ X12 @ X14))
% 0.20/0.51          | ((X14) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) != (k1_mcart_1 @ sk_C))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      ((((sk_C) = (k1_mcart_1 @ sk_C)) | ((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((((sk_C) = (k1_mcart_1 @ sk_C))) <= ((((sk_C) = (k1_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('split', [status(esa)], ['19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((((sk_C) = (k2_mcart_1 @ sk_C))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('split', [status(esa)], ['19'])).
% 0.20/0.51  thf('22', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (((X12) = (k1_xboole_0))
% 0.20/0.51          | ((X13) != (k2_mcart_1 @ X13))
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (k2_zfmisc_1 @ X12 @ X14))
% 0.20/0.51          | ((X14) = (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t26_mcart_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) != (k2_mcart_1 @ sk_C))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((((sk_C) != (sk_C))
% 0.20/0.51         | ((sk_A) = (k1_xboole_0))
% 0.20/0.51         | ((sk_B_1) = (k1_xboole_0)))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.51         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.20/0.51        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ (k2_mcart_1 @ X9) @ X11)
% 0.20/0.51          | ~ (r2_hidden @ X9 @ (k2_zfmisc_1 @ X10 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.20/0.51        | (r2_hidden @ (k2_mcart_1 @ sk_C) @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.20/0.51      inference('simplify_reflect+', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('31', plain, ((r2_hidden @ (k2_mcart_1 @ sk_C) @ sk_B_1)),
% 0.20/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf('33', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0))))
% 0.20/0.51         <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '33'])).
% 0.20/0.51  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      ((((sk_A) = (k1_xboole_0))) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ k1_xboole_0)) <= ((((sk_C) = (k2_mcart_1 @ sk_C))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.51  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('40', plain, (~ (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((((sk_C) = (k1_mcart_1 @ sk_C))) | (((sk_C) = (k2_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('split', [status(esa)], ['19'])).
% 0.20/0.51  thf('42', plain, ((((sk_C) = (k1_mcart_1 @ sk_C)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.20/0.51  thf('43', plain, (((sk_C) = (k1_mcart_1 @ sk_C))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['20', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      ((((sk_B_1) = (k1_xboole_0))
% 0.20/0.51        | ((sk_C) != (sk_C))
% 0.20/0.51        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '43'])).
% 0.20/0.51  thf('45', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['44'])).
% 0.20/0.51  thf('46', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.51  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('49', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.51  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.51  thf('51', plain, ($false),
% 0.20/0.51      inference('demod', [status(thm)], ['15', '49', '50'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
