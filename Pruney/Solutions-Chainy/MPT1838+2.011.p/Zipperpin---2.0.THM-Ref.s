%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uVGZEiKQSL

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:16 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   72 (  95 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   16
%              Number of atoms          :  427 ( 651 expanded)
%              Number of equality atoms :   49 (  70 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( X24
        = ( k6_domain_1 @ X24 @ ( sk_B_1 @ X24 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('2',plain,(
    ! [X24: $i] :
      ( ~ ( v1_zfmisc_1 @ X24 )
      | ( m1_subset_1 @ ( sk_B_1 @ X24 ) @ X24 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( ( k6_domain_1 @ X22 @ X23 )
        = ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
        = ( k1_tarski @ ( sk_B_1 @ X0 ) ) )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t44_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X17 = X18 )
      | ( ( k1_tarski @ X19 )
       != ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t44_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = sk_B_2 )
      | ( sk_B_2 = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    r1_tarski @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_hidden @ ( sk_B @ sk_A ) @ sk_B_2 ),
    inference(clc,[status(thm)],['15','16'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('18',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('21',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ sk_A ) ) @ sk_B_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('23',plain,
    ( ( k2_xboole_0 @ sk_B_2 @ ( k1_tarski @ ( sk_B @ sk_A ) ) )
    = sk_B_2 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('25',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ X21 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    sk_A != sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != sk_B_2 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k6_domain_1 @ X0 @ ( sk_B_1 @ X0 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B_2 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_zfmisc_1 @ X0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_zfmisc_1 @ sk_B_2 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    v1_zfmisc_1 @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X4: $i] :
      ( ( v1_xboole_0 @ X4 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X14 ) @ X16 )
      | ~ ( r2_hidden @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k1_tarski @ ( sk_B @ X0 ) ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uVGZEiKQSL
% 0.16/0.37  % Computer   : n022.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:12:26 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 267 iterations in 0.127s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.39/0.61  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.61  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.39/0.61  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.39/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.61  thf(t1_tex_2, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.39/0.61           ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61          ( ![B:$i]:
% 0.39/0.61            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v1_zfmisc_1 @ B ) ) =>
% 0.39/0.61              ( ( r1_tarski @ A @ B ) => ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t1_tex_2])).
% 0.39/0.61  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d1_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.61       ( ( v1_zfmisc_1 @ A ) <=>
% 0.39/0.61         ( ?[B:$i]:
% 0.39/0.61           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      (![X24 : $i]:
% 0.39/0.61         (~ (v1_zfmisc_1 @ X24)
% 0.39/0.61          | ((X24) = (k6_domain_1 @ X24 @ (sk_B_1 @ X24)))
% 0.39/0.61          | (v1_xboole_0 @ X24))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X24 : $i]:
% 0.39/0.61         (~ (v1_zfmisc_1 @ X24)
% 0.39/0.61          | (m1_subset_1 @ (sk_B_1 @ X24) @ X24)
% 0.39/0.61          | (v1_xboole_0 @ X24))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.39/0.61  thf(redefinition_k6_domain_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.39/0.61       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X22 : $i, X23 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X22)
% 0.39/0.61          | ~ (m1_subset_1 @ X23 @ X22)
% 0.39/0.61          | ((k6_domain_1 @ X22 @ X23) = (k1_tarski @ X23)))),
% 0.39/0.61      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.39/0.61  thf('4', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X0)
% 0.39/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.61          | ((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.39/0.61          | (v1_xboole_0 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.61  thf('5', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) = (k1_tarski @ (sk_B_1 @ X0)))
% 0.39/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.61          | (v1_xboole_0 @ X0))),
% 0.39/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.39/0.61  thf('6', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t12_xboole_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.61  thf('8', plain, (((k2_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.39/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.61  thf(t44_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.39/0.61          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.39/0.61          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.39/0.61         (((X17) = (k1_xboole_0))
% 0.39/0.61          | ((X18) = (k1_xboole_0))
% 0.39/0.61          | ((X17) = (X18))
% 0.39/0.61          | ((k1_tarski @ X19) != (k2_xboole_0 @ X17 @ X18)))),
% 0.39/0.61      inference('cnf', [status(esa)], [t44_zfmisc_1])).
% 0.39/0.61  thf('10', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (((k1_tarski @ X0) != (sk_B_2))
% 0.39/0.61          | ((sk_A) = (sk_B_2))
% 0.39/0.61          | ((sk_B_2) = (k1_xboole_0))
% 0.39/0.61          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.61  thf(d1_xboole_0, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.61  thf('12', plain, ((r1_tarski @ sk_A @ sk_B_2)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d3_tarski, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.39/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X5 @ X6)
% 0.39/0.61          | (r2_hidden @ X5 @ X7)
% 0.39/0.61          | ~ (r1_tarski @ X6 @ X7))),
% 0.39/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.39/0.61  thf('14', plain,
% 0.39/0.61      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B_2) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['12', '13'])).
% 0.39/0.61  thf('15', plain,
% 0.39/0.61      (((v1_xboole_0 @ sk_A) | (r2_hidden @ (sk_B @ sk_A) @ sk_B_2))),
% 0.39/0.61      inference('sup-', [status(thm)], ['11', '14'])).
% 0.39/0.61  thf('16', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('17', plain, ((r2_hidden @ (sk_B @ sk_A) @ sk_B_2)),
% 0.39/0.61      inference('clc', [status(thm)], ['15', '16'])).
% 0.39/0.61  thf(l1_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.39/0.61  thf('18', plain,
% 0.39/0.61      (![X14 : $i, X16 : $i]:
% 0.39/0.61         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.61  thf('19', plain, ((r1_tarski @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2)),
% 0.39/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (((k2_xboole_0 @ (k1_tarski @ (sk_B @ sk_A)) @ sk_B_2) = (sk_B_2))),
% 0.39/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf(commutativity_k2_xboole_0, axiom,
% 0.39/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      (((k2_xboole_0 @ sk_B_2 @ (k1_tarski @ (sk_B @ sk_A))) = (sk_B_2))),
% 0.39/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.61  thf(t49_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i]:
% 0.39/0.61     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X20 : $i, X21 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ (k1_tarski @ X20) @ X21) != (k1_xboole_0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.39/0.61  thf('26', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('27', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '26'])).
% 0.39/0.61  thf('28', plain, (((sk_A) != (sk_B_2))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      (![X0 : $i]: (((k1_tarski @ X0) != (sk_B_2)) | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.61      inference('simplify_reflect-', [status(thm)], ['10', '27', '28'])).
% 0.39/0.61  thf('30', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (((k6_domain_1 @ X0 @ (sk_B_1 @ X0)) != (sk_B_2))
% 0.39/0.61          | (v1_xboole_0 @ X0)
% 0.39/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.61          | ((sk_A) = (k1_xboole_0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['5', '29'])).
% 0.39/0.61  thf('31', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (((X0) != (sk_B_2))
% 0.39/0.61          | (v1_xboole_0 @ X0)
% 0.39/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.61          | ((sk_A) = (k1_xboole_0))
% 0.39/0.61          | ~ (v1_zfmisc_1 @ X0)
% 0.39/0.61          | (v1_xboole_0 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '30'])).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      ((((sk_A) = (k1_xboole_0))
% 0.39/0.61        | ~ (v1_zfmisc_1 @ sk_B_2)
% 0.39/0.61        | (v1_xboole_0 @ sk_B_2))),
% 0.39/0.61      inference('simplify', [status(thm)], ['31'])).
% 0.39/0.61  thf('33', plain, ((v1_zfmisc_1 @ sk_B_2)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('34', plain, ((((sk_A) = (k1_xboole_0)) | (v1_xboole_0 @ sk_B_2))),
% 0.39/0.61      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.39/0.61  thf('35', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 0.39/0.61      inference('clc', [status(thm)], ['34', '35'])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (![X4 : $i]: ((v1_xboole_0 @ X4) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (![X14 : $i, X16 : $i]:
% 0.39/0.61         ((r1_tarski @ (k1_tarski @ X14) @ X16) | ~ (r2_hidden @ X14 @ X16))),
% 0.39/0.61      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      (![X9 : $i, X10 : $i]:
% 0.39/0.61         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X0)
% 0.39/0.61          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.39/0.61      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.39/0.61  thf('43', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((v1_xboole_0 @ X0)
% 0.39/0.61          | ((k2_xboole_0 @ X0 @ (k1_tarski @ (sk_B @ X0))) = (X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.61  thf('44', plain,
% 0.39/0.61      (![X0 : $i, X1 : $i]:
% 0.39/0.61         ((k2_xboole_0 @ X1 @ (k1_tarski @ X0)) != (k1_xboole_0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (v1_xboole_0 @ X0))),
% 0.39/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.61  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.61      inference('simplify', [status(thm)], ['45'])).
% 0.39/0.61  thf('47', plain, ($false),
% 0.39/0.61      inference('demod', [status(thm)], ['0', '36', '46'])).
% 0.39/0.61  
% 0.39/0.61  % SZS output end Refutation
% 0.39/0.61  
% 0.39/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
