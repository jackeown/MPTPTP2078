%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vt6Pq9kVic

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:21 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   63 (  87 expanded)
%              Number of leaves         :   22 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  368 ( 641 expanded)
%              Number of equality atoms :   25 (  48 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t1_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_zfmisc_1 @ B ) )
         => ( ( r1_tarski @ A @ B )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_zfmisc_1 @ B ) )
           => ( ( r1_tarski @ A @ B )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_tex_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('1',plain,(
    ! [X18: $i] :
      ( ~ ( v1_zfmisc_1 @ X18 )
      | ( X18
        = ( k6_domain_1 @ X18 @ ( sk_B @ X18 ) ) )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X18: $i] :
      ( ~ ( v1_zfmisc_1 @ X18 )
      | ( m1_subset_1 @ ( sk_B @ X18 ) @ X18 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B @ X0 ) )
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ( X0
        = ( k1_tarski @ ( sk_B @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ ( k1_tarski @ X13 ) )
      | ( X12
       != ( k1_tarski @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,(
    ! [X13: $i] :
      ( r1_tarski @ ( k1_tarski @ X13 ) @ ( k1_tarski @ X13 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','10'])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12
        = ( k1_tarski @ X11 ) )
      | ( X12 = k1_xboole_0 )
      | ~ ( r1_tarski @ X12 @ ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k1_tarski @ ( sk_B @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_zfmisc_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','21'])).

thf('23',plain,(
    v1_zfmisc_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( sk_A = sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['26','27'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ C @ A )
          & ( r1_tarski @ C @ B )
          & ( r1_xboole_0 @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Vt6Pq9kVic
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:33:36 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 46 iterations in 0.026s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.47  thf(t1_tex_2, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.19/0.47           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.19/0.47              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.19/0.47  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(d1_tex_2, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.47       ( ( v1_zfmisc_1 @ A ) <=>
% 0.19/0.47         ( ?[B:$i]:
% 0.19/0.47           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      (![X18 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X18)
% 0.19/0.47          | ((X18) = (k6_domain_1 @ X18 @ (sk_B @ X18)))
% 0.19/0.47          | (v1_xboole_0 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X18 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X18)
% 0.19/0.47          | (m1_subset_1 @ (sk_B @ X18) @ X18)
% 0.19/0.47          | (v1_xboole_0 @ X18))),
% 0.19/0.47      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.19/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X16 : $i, X17 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X16)
% 0.19/0.47          | ~ (m1_subset_1 @ X17 @ X16)
% 0.19/0.47          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | ((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((k6_domain_1 @ X0 @ (sk_B @ X0)) = (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (((X0) = (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['1', '5'])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.19/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ((X0) = (k1_tarski @ (sk_B @ X0))))),
% 0.19/0.47      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.47  thf(l3_zfmisc_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (![X12 : $i, X13 : $i]:
% 0.19/0.47         ((r1_tarski @ X12 @ (k1_tarski @ X13)) | ((X12) != (k1_tarski @ X13)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      (![X13 : $i]: (r1_tarski @ (k1_tarski @ X13) @ (k1_tarski @ X13))),
% 0.19/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         ((r1_tarski @ X0 @ (k1_tarski @ (sk_B @ X0)))
% 0.19/0.47          | (v1_xboole_0 @ X0)
% 0.19/0.47          | ~ (v1_zfmisc_1 @ X0))),
% 0.19/0.47      inference('sup+', [status(thm)], ['8', '10'])).
% 0.19/0.47  thf('12', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t1_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.47       ( r1_tarski @ A @ C ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.47         (~ (r1_tarski @ X4 @ X5)
% 0.19/0.47          | ~ (r1_tarski @ X5 @ X6)
% 0.19/0.47          | (r1_tarski @ X4 @ X6))),
% 0.19/0.47      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r1_tarski @ sk_B_1 @ X0))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain,
% 0.19/0.47      ((~ (v1_zfmisc_1 @ sk_B_1)
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.47        | (r1_tarski @ sk_A @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['11', '14'])).
% 0.19/0.47  thf('16', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('17', plain,
% 0.19/0.47      (((v1_xboole_0 @ sk_B_1)
% 0.19/0.47        | (r1_tarski @ sk_A @ (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.19/0.47      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.47  thf('18', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('19', plain, ((r1_tarski @ sk_A @ (k1_tarski @ (sk_B @ sk_B_1)))),
% 0.19/0.47      inference('clc', [status(thm)], ['17', '18'])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      (![X11 : $i, X12 : $i]:
% 0.19/0.47         (((X12) = (k1_tarski @ X11))
% 0.19/0.47          | ((X12) = (k1_xboole_0))
% 0.19/0.47          | ~ (r1_tarski @ X12 @ (k1_tarski @ X11)))),
% 0.19/0.47      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.47  thf('21', plain,
% 0.19/0.47      ((((sk_A) = (k1_xboole_0)) | ((sk_A) = (k1_tarski @ (sk_B @ sk_B_1))))),
% 0.19/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.47  thf('22', plain,
% 0.19/0.47      ((((sk_A) = (sk_B_1))
% 0.19/0.47        | (v1_xboole_0 @ sk_B_1)
% 0.19/0.47        | ~ (v1_zfmisc_1 @ sk_B_1)
% 0.19/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['7', '21'])).
% 0.19/0.47  thf('23', plain, ((v1_zfmisc_1 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('24', plain,
% 0.19/0.47      ((((sk_A) = (sk_B_1)) | (v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.47  thf('25', plain, (((sk_A) != (sk_B_1))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('26', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.47      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.19/0.47  thf('27', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('28', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.47      inference('clc', [status(thm)], ['26', '27'])).
% 0.19/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.47  thf('29', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.47  thf('30', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.19/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.47  thf(t3_xboole_0, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.19/0.47       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.19/0.47            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.19/0.47  thf('31', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.19/0.47  thf(t7_ordinal1, axiom,
% 0.19/0.47    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.47  thf('32', plain,
% 0.19/0.47      (![X14 : $i, X15 : $i]:
% 0.19/0.47         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 0.19/0.47      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.19/0.47  thf('33', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.19/0.47  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['30', '33'])).
% 0.19/0.47  thf(t68_xboole_1, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.19/0.47       ( ~( ( r1_tarski @ C @ A ) & ( r1_tarski @ C @ B ) & 
% 0.19/0.47            ( r1_xboole_0 @ A @ B ) ) ) ))).
% 0.19/0.47  thf('35', plain,
% 0.19/0.47      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.47         (~ (r1_xboole_0 @ X8 @ X9)
% 0.19/0.47          | (v1_xboole_0 @ X10)
% 0.19/0.47          | ~ (r1_tarski @ X10 @ X8)
% 0.19/0.47          | ~ (r1_tarski @ X10 @ X9))),
% 0.19/0.47      inference('cnf', [status(esa)], [t68_xboole_1])).
% 0.19/0.47  thf('36', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i]:
% 0.19/0.47         (~ (r1_tarski @ X1 @ k1_xboole_0)
% 0.19/0.47          | ~ (r1_tarski @ X1 @ X0)
% 0.19/0.47          | (v1_xboole_0 @ X1))),
% 0.19/0.47      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.47  thf('37', plain,
% 0.19/0.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | (v1_xboole_0 @ X0))),
% 0.19/0.47      inference('condensation', [status(thm)], ['36'])).
% 0.19/0.47  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.47      inference('sup-', [status(thm)], ['29', '37'])).
% 0.19/0.47  thf('39', plain, ($false),
% 0.19/0.47      inference('demod', [status(thm)], ['0', '28', '38'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
